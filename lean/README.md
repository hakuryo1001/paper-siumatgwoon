# Siumatgwoon Formalization

This directory contains a Lean 4 formalization of Siumatgwoon (Metaphysic) structures, based on the definitions in `chapters/02-definitions.tex`.

## Structure

- `Siumatgwoon.lean`: Main formalization file containing:
  - Definition of `Siumatgwoon` with axioms (reflexivity, totality, transitivity, composition constitution)
  - Definition of `SimpleSiumatgwoon` with additional axioms (antisymmetry, finite composition, finite constitution, unique decomposition)
  - Definitions of atomics, elementals, generators, and 系 (Hai) sets
  - Various lemmas and theorems (some with proofs, some with `sorry` placeholders)

## Key Definitions

### Siumatgwoon
A structure with:
- Composition operation `* : S → S → S`
- Constitution relation `| : S → S → Prop`
- Axioms: reflexivity, totality, transitivity, composition constitution

### Simple Siumatgwoon
Extends Siumatgwoon with:
- Antisymmetry
- Finite composition
- Finite constitution
- Unique decomposition

### Atomics
Elements where only themselves constitute them: `IsAtomic a := ∀ x, x | a → x = a`

### Elementals
Elements that cannot be decomposed non-trivially from their constituents.

### 系 (Hai) Sets
The set `⟨x⟩` of all elements `s` such that `x | s` but `s` cannot be written as `x * y₁ * ... * yₙ`.

## Usage

To use this formalization, you'll need:
1. Lean 4 installed
2. Mathlib dependencies

Example:
```lean
import Siumatgwoon

variable {S : Type*} (M : SimpleSiumatgwoon S)

-- Check if an element is atomic
#check SimpleSiumatgwoon.IsAtomic M

-- Get the 系 set for an element
#check SimpleSiumatgwoon.Hai M
```

## Status

Many theorems have `sorry` placeholders and need to be completed. The structure and definitions are in place, ready for proving.

