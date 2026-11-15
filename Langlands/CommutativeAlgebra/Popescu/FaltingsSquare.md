# Naturality of the Jacobi–Zariski connecting map for a local map `A → A'`

This module provides the left square of the "big diagram" in Faltings' proof of Stacks, More on
Algebra, Proposition 15.36.1 (07E5), (2) ⇒ (4). All declarations live in
`Langlands.CommutativeAlgebra.Popescu.Faltings`. Setting: `A → A'` is a local homomorphism of
local rings, with residue fields `κ = κ(A)` and `κ' = κ(A')`.

## `h1_map_square`

`H₁(L_{κ/A}) → H₁(L_{κ'/A'})` factors as `H₁(L_{κ/A}) → H₁(L_{κ'/A}) → H₁(L_{κ'/A'})`. Both are
maps induced by homs of presentations, so this follows from functoriality
(`Extension.H1Cotangent.map_comp_apply`). Mathlib's `map_eq` shows that the map does not depend on
the chosen hom.

## `δ_square`

For `x ∈ H₁(L_{κ/A})`:

`δ_{A'}(H₁(map)(x)) = baseMap(cancelBaseChange(1 ⊗ δ_A x))`.

Here `δ_A : H₁(L_{κ/A}) → κ ⊗_A Ω_{A/ℤ}` is the connecting map. `cancelBaseChange` identifies
`κ' ⊗_κ (κ ⊗_A Ω_{A/ℤ})` with `κ' ⊗_A Ω_{A/ℤ}`, and
`baseMap : κ' ⊗_A Ω_{A/ℤ} → κ' ⊗_{A'} Ω_{A'/ℤ}` is the map induced by `A → A'`.

Proof:
1. Rewrite with `h1_map_square`.
2. Use naturality of `δ` in the middle ring (`δ_map_base`, for `A → A'` with target `κ'`).
3. Use naturality in the target field (`FieldH1.δ_map`, for `κ → κ'`). This lemma is in the Library
   module `Langlands.CommutativeAlgebra.Popescu.FieldH1CotangentInjectiveProof`, the proof of
   `FieldH1CotangentInjectiveStatement` (Stacks 07E2).
