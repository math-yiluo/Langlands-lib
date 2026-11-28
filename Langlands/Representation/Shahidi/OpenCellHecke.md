# Minuscule Hecke operators on lifted functions

Module `Langlands.Representation.Shahidi.OpenCellHecke`, namespace
`Langlands.Shahidi.OpenCell`.

## Contents

- `IsBlockEquivariant`, `IsRightIntegral`: left equivariance under the upper unipotent group by
  `θ'(u) = θ₁(u₁₁) θ₂(u₂₂)` and right invariance under integral matrices.
- `eval_torus_eq_zero_of_not_antitone_first` (resp. `_second`): a block-equivariant,
  right-integral function vanishes at every torus point `ϖ^ν` whose first (resp. second) block
  of exponents is not antitone, provided the block character `θ₁` (resp. `θ₂`) is nontrivial
  on each simple root group over `ϖ⁻¹𝒪`: for every simple root `i` there is `x` with
  `|x| |ϖ| ≤ 1` and `θ₁(adjacentUnit i x) ≠ 1`. Under these character conditions for both
  blocks, such a function is therefore determined by its values at the torus points that are
  antitone on each block.
- `eq_of_eval_torus`: two block-equivariant right-integral functions that agree at every torus
  point agree (Iwasawa decomposition; no character condition).
- `IsLeviEquivariant θ₁ θ₂ Φ`: left equivariance of a Levi function under the upper unipotent
  groups of the two blocks. For a Levi-invariant `Φ`: `isRightIntegral_liftFunction` (the lift
  is right integral) and `liftFunction_torus` (the lift at `ϖ^μ` is `Φ` at the two diagonal torus
  blocks); for a Levi-invariant and Levi-equivariant `Φ`: `liftFunction_unipotent_mul`,
  `isBlockEquivariant_liftFunction` (the lift is block-equivariant for `θ₁`, `θ₂`).
- `liftFunction_torus_mul_labelledRep`, `sum_liftFunction_torus_mul_labelledRep`: for a
  Levi-invariant, Levi-equivariant `Φ` whose block characters `θ₁`, `θ₂` are integrally trivial,
  and coset labels `σ` with integral values, at a torus point `ϖ^ν` with `ν` antitone on each
  block the translates by the minuscule coset representatives are the values at
  `ϖ^(ν + 1_S)`, weighted (in the sum) by the radical-pair counts `|Λ|^(#RadicalPairs S)`.

## Provenance

Derived from the Library's minuscule coset representatives (`Unramified.MinusculeCosets`) and
the vanishing of Whittaker-type functions off dominant torus points
(`RankinSelberg.UnramifiedWhittakerCells`).
