# Dominant torus sandwiches with a unipotent left factor

Module `Langlands.Representation.RankinSelberg.TwoBlockJacquetConvergence.UnipotentSandwich`,
namespace `Langlands.RankinSelberg.TwoBlockConvergence`.

Author: Worker 886.

This is a helper module for the proof of
`Langlands.RankinSelberg.TwoBlockJacquetConvergenceStatement` (JPSS 1983,
Section (4.6)). It is used by the module `DominantGrowth`, where the left
factor must be upper unipotent so that a Whittaker-type functional only
changes by a character value of absolute value one.

## Provenance

The content is internal to this proof. It refines the published
`Langlands.GeneralLinear.exists_dominant_sandwich`
(`Langlands.Group.GL.PrincipalLevelDominance`) and follows its proof. That
result writes `ϖ^lam₁ g ϖ^lam₂` as `(x d) (ϖ^lam₁ ϖ^lam₂) y`, where `d` is
diagonal in the level. Here `d` is moved into the right factor instead, since
it commutes with diagonal matrices.

## Shared conjugation lemmas

The proof reuses `Langlands.GeneralLinear.principal_upper_conj` and
`Langlands.GeneralLinear.principal_lower_inv_conj` from
`Langlands.Group.GL.PrincipalLevelDominance`. Their statements and proofs are
unchanged; integration made these two existing theorems public and removed
this module's copied private conjugation section. If the block scalar ratios
`a i / a j` for `i < j` are integral, conjugating an upper unipotent element
of `K(I)` by that block scalar stays in `K(I)`, as does conjugating a lower
unipotent element by its inverse. The shared proofs compare matrix entries.

`diagonalUnits_conj_mem_upperUnipotent`: conjugating an upper unipotent
matrix by an invertible diagonal matrix gives an upper unipotent matrix,
again checked entrywise.

## Main result (section `Sandwich`)

`exists_unipotent_sandwich`: let `k` be a valued field, `ϖ` a unit with
`v(ϖ) ≤ 1`, `a > 0`, `P = principalLevelSubgroup k n a` and
`lam₁, lam₂ : Fin (n + 1) → ℤ` antitone. Then for every `g ∈ P` there are
`x ∈ P` upper unipotent and `y ∈ P` with

`torus ϖ lam₁ * g * torus ϖ lam₂ = x * (torus ϖ lam₁ * torus ϖ lam₂) * y`.

Proof as implemented:

1. Apply the published Iwahori factorization
   `BlockShape.principalLevelSubgroup_iwahoriProduct_surjective` for the
   singleton block shape to `g⁻¹ ∈ P`. This gives `g⁻¹ = l d u` with `l`
   lower unipotent, `d` diagonal and `u` upper unipotent, each in `P`, so
   `g = u⁻¹ d⁻¹ l⁻¹`.
2. Write `δᵢ = torus ϖ lamᵢ` as a block scalar (`torus_eq_blockScalar`, published).
   The ratios of `δᵢ` are integral by antitonicity (`ratio_mem_integer`,
   published).
3. Put `x = δ₁ u⁻¹ δ₁⁻¹` and `y = d⁻¹ (δ₂⁻¹ l⁻¹ δ₂)`. The conjugation lemmas
   give `x ∈ P` and `δ₂⁻¹ l⁻¹ δ₂ ∈ P`, so `y ∈ P`. Also `x` is upper unipotent.
4. The Levi element `d⁻¹` commutes with the block scalar `δ₂`
   (`blockScalarLevi_commute`). Hence
   `δ₁ (u⁻¹ d⁻¹ l⁻¹) δ₂ = (δ₁ u⁻¹ δ₁⁻¹)(δ₁ δ₂)(d⁻¹ δ₂⁻¹ l⁻¹ δ₂)`, a group identity
   closed by `group`.
