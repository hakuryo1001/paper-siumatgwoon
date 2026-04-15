/-
  Formalization of Siumatgwoon (Metaphysic) structures
  Based on definitions in chapters/02-definitions.tex
-/

import Mathlib.Data.List.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Set.Basic

/-- A Siumatgwoon (or Metaphysic) is a set S with composition and constitution relations -/
structure Siumatgwoon (S : Type*) where
  comp : S → S → S  -- Composition: a * b
  const : S → S → Prop  -- Constitution: a | b (a constitutes b)

  -- Axiom: Reflexivity
  reflexivity : ∀ a : S, const a a

  -- Axiom: Totality (exactly one of a|b or not a|b holds)
  -- This is actually just the law of excluded middle, but we state it explicitly
  totality : ∀ a b : S, const a b ∨ ¬ const a b

  -- Axiom: Transitivity
  transitivity : ∀ a b c : S, const a b → const b c → const a c

  -- Axiom: Composition Constitution
  comp_const : ∀ a b c : S, comp a b = c → const a c ∧ const b c

namespace Siumatgwoon

variable {S : Type*} (M : Siumatgwoon S)

/-- Notation for composition -/
infixl:70 " * " => M.comp

/-- Notation for constitution -/
infix:50 " | " => M.const

/-- A Simple Siumatgwoon extends a Siumatgwoon with additional axioms -/
structure SimpleSiumatgwoon (S : Type*) extends Siumatgwoon S where
  -- Axiom: Antisymmetry
  antisymmetry : ∀ a b : S, toSiumatgwoon.const a b → toSiumatgwoon.const b a → a = b

  -- Axiom: Finite Composition
  -- Every object is finitely composed: x = y₁ * y₂ * ... * yₙ for some finite n
  finite_composition : ∀ x : S, ∃ (l : List S), l.length > 0 ∧
    (match l with
    | [] => False
    | [y] => y = x
    | y :: ys => List.foldl toSiumatgwoon.comp y ys = x)

  -- Axiom: Finite Constitution
  -- For any x, there are only finitely many y such that y | x
  finite_constitution : ∀ x : S, {y : S | toSiumatgwoon.const y x}.Finite

  -- Axiom: Unique Decomposition
  -- The longest decomposition is unique
  -- We need to formalize "longest decomposition" properly
  unique_decomposition : ∀ x : S, ∃! (l : List S),
    (match l with
    | [] => False
    | [y] => y = x
    | y :: ys => List.foldl toSiumatgwoon.comp y ys = x) ∧
    (∀ (l' : List S),
      (match l' with
      | [] => False
      | [y] => y = x
      | y :: ys => List.foldl toSiumatgwoon.comp y ys = x) →
      l'.length ≤ l.length)

namespace SimpleSiumatgwoon

variable {S : Type*} (M : SimpleSiumatgwoon S)

/-- Notation for composition in simple siumatgwoon -/
infixl:70 " * " => M.toSiumatgwoon.comp

/-- Notation for constitution in simple siumatgwoon -/
infix:50 " | " => M.toSiumatgwoon.const

/-- Helper function to compose a non-empty list of elements -/
def compose_list (l : List S) (h : l.length > 0) : S :=
  match l with
  | [x] => x
  | x :: xs => List.foldl M.toSiumatgwoon.comp x xs
  | [] => by exfalso; exact Nat.not_lt_zero _ h

/-- An element is a compound if it is not elemental -/
def IsCompound (x : S) : Prop :=
  ¬ IsElemental M x

/-- An element is atomic if only itself constitutes it -/
def IsAtomic (a : S) : Prop :=
  ∀ x : S, M.toSiumatgwoon.const x a → x = a

/-- The set of all atomic elements -/
def Atomics : Set S := {a | IsAtomic M a}

/-- An element is elemental if it has no non-trivial decomposition -/
/-- For all x₁, x₂, ..., xₙ where x₁, x₂, ..., xₙ | e,
    we cannot find a finite sequence drawn from x₁, x₂, ..., xₙ such that it composes e -/
def IsElemental (e : S) : Prop :=
  ∀ (constituents : Finset S),
    (∀ x ∈ constituents, M.toSiumatgwoon.const x e) →
    ¬ (∃ (seq : List S) (h : seq.length > 0),
        (∀ s ∈ seq, s ∈ constituents) ∧
        compose_list M seq h = e)

/-- The set of all elemental elements -/
def Elementals : Set S := {e | IsElemental M e}

/-- A set G is a generator if every object can be expressed as a composition from G -/
def IsGenerator (G : Set S) : Prop :=
  ∀ x : S, ∃ (seq : List S) (h : seq.length > 0),
    (∀ g ∈ seq, g ∈ G) ∧
    compose_list M seq h = x

/-- The 系 (Hai) set for an element x -/
/-- ⟨x⟩ := {s ∈ S : x|s but ∄ y₁, y₂, ..., yₙ ∈ S such that s = x*y₁*y₂*...*yₙ} -/
def Hai (x : S) : Set S :=
  {s | M.toSiumatgwoon.const x s ∧
       ¬ (∃ (ys : List S),
           compose_list M (x :: ys) (by simp) = s)}

/-- Notation for 系 sets -/
notation "⟨" x "⟩" => Hai M x

/-- The 系 set for a set X -/
def HaiSet (X : Set S) : Set S :=
  ⋃ x ∈ X, Hai M x

/-- Notation for 系 sets of sets -/
notation "⟨" X "⟩" => HaiSet M X

-- Basic lemmas and theorems

/-- Lemma: An object is in its own 系 set -/
theorem self_in_hai (x : S) : x ∈ ⟨x⟩ := by
  unfold Hai
  simp
  constructor
  · exact M.toSiumatgwoon.reflexivity x
  · intro h
    obtain ⟨ys, h_eq⟩ := h
    -- If x = x * y₁ * ... * yₙ, then by comp_const, x | x * y₁ * ... * yₙ = x
    -- This is always true by reflexivity, but we need to show it's impossible
    -- Actually, the definition says we can't write x as x * y₁ * ... * yₙ
    -- But x itself is just x, not x * something, so this should hold
    -- The issue is we need to ensure ys is non-empty or handle the case differently
    sorry

/-- Lemma: Atomics are elementals in simple siumatgwoons -/
theorem atomics_are_elementals : Atomics M ⊆ Elementals M := by
  intro a ha
  unfold Elementals IsElemental
  simp
  intro x₁ x₂ x₃ xs hx₁ hx₂ hx₃ hxs
  -- If a is atomic, then x₁ = a, x₂ = a, x₃ = a, etc.
  -- But then we can't compose them to get a non-trivially
  sorry

/-- Lemma: Every elemental has an atomic constituent -/
theorem every_elemental_has_atomic_constituent (e : S) (he : e ∈ Elementals M) :
    ∃ a ∈ Atomics M, M.toSiumatgwoon.const a e := by
  -- Proof by contradiction using finite_constitution
  sorry

/-- Theorem: Elementals are a generator set -/
theorem elementals_are_generator : IsGenerator M (Elementals M) := by
  unfold IsGenerator
  intro x
  -- Use the fact that compounds are composed by elementals
  sorry

/-- Theorem: The elementals are identical to A-系 in simple siumatgwoons -/
theorem elementals_eq_hai_atomics : Elementals M = HaiSet M (Atomics M) := by
  ext e
  constructor
  · intro he
    -- If e is elemental, it has an atomic constituent
    obtain ⟨a, ha, ha_e⟩ := every_elemental_has_atomic_constituent M e he
    exact Set.mem_iUnion.mpr ⟨a, Set.mem_iUnion.mpr ⟨ha, sorry⟩⟩
  · intro he
    -- If e is in ⟨A⟩, then e is elemental
    sorry

/-- Lemma: All objects are either elementals or compounds -/
theorem elementals_or_compounds (x : S) : x ∈ Elementals M ∨ IsCompound M x := by
  by_cases h : IsElemental M x
  · left; exact h
  · right; exact h

/-- Lemma: Compounds are composed by elementals -/
theorem compounds_composed_by_elementals (x : S) (hx : IsCompound M x) :
    ∃ (seq : List S) (h : seq.length > 0),
      (∀ e ∈ seq, e ∈ Elementals M) ∧
      compose_list M seq h = x := by
  -- Proof uses finite_constitution and contradiction
  sorry

/-- Theorem: Unique decomposition into elementals -/
theorem unique_decomposition_into_elementals (x : S) :
    ∃! (seq : List S) (h : seq.length > 0),
      (∀ e ∈ seq, e ∈ Elementals M) ∧
      compose_list M seq h = x := by
  -- Uses unique_decomposition axiom and elementals_are_generator
  sorry

/-- Lemma: If a|b, then ⟨b⟩ ⊆ ⟨a⟩ -/
theorem hai_subset_constituent (a b : S) (h : M.toSiumatgwoon.const a b) :
    ⟨b⟩ ⊆ ⟨a⟩ := by
  intro x hx
  unfold Hai at hx ⊢
  simp at hx ⊢
  constructor
  · -- x | b and a | b implies a | x by transitivity
    have : M.toSiumatgwoon.const a x := by
      apply M.toSiumatgwoon.transitivity a b x
      exact h
      exact hx.1
    exact this
  · -- Need to show x cannot be written as a * y₁ * ... * yₙ
    sorry

/-- Theorem: Indempotence of emergence -/
theorem indempotence_of_emergence (x : S) :
    HaiSet M (Hai M x) = Hai M x := by
  -- ⟨⟨x⟩⟩ = ⟨x⟩
  ext s
  constructor
  · intro hs
    -- If s ∈ ⟨⟨x⟩⟩, then s ∈ ⟨x⟩
    sorry
  · intro hs
    -- If s ∈ ⟨x⟩, then s ∈ ⟨⟨x⟩⟩
    exact Set.mem_iUnion.mpr ⟨s, Set.mem_iUnion.mpr ⟨hs, self_in_hai M s⟩⟩

/-- Theorem: Every 系 set is a subset of a 系 set whose head is atomic -/
theorem hai_subset_of_atomic_hai (x : S) :
    ∃ a ∈ Atomics M, ⟨x⟩ ⊆ ⟨a⟩ := by
  -- Uses every_elemental_has_atomic_constituent
  sorry

end SimpleSiumatgwoon

end Siumatgwoon
