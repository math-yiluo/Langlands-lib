/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.EtaleCohomology.PoincareDuality.Frobenius.Equivariance
public import WeilConjectures.EtaleCohomology.PoincareDuality.Frobenius.Pairings
public import WeilConjectures.EtaleCohomology.PoincareDuality.Frobenius.Reciprocity

/-!
# Frobenius: equivariance, similitude, reciprocity

Let `a : X ⟶ Y` admit a compactification, `γ : Λ_X(d)[2d] ≅ Ra^! Λ_Y` be a Tate orientation and
`g : X ⟶ X`, `h : Y ⟶ Y` with `g ≫ a = a ≫ h` (cartesian). In the setting of the Poincaré
duality chapter `Y = Spec k`, `X = X₀ ×_{k₀} k` and `g`, `h` are the geometric Frobenius
automorphisms. A strict Weil complex `(K, φ)` on `X` gives Weil data on `RΓ_c(X, K) = Ra_! K`
and on `RΓ(X, M) = Ra_* M`, whose Frobenius operators are the geometric Frobenius `F_{c,K}` on
`H^i_c(X, K)` and `F_M` on `H^j(X, M)`. This file proves the Frobenius statements of
`theorem-poincare-duality-frobenius`.

**(a) Equivariance and similitude.** The derived Poincaré pairing `β_K` is a morphism of Weil
objects, so the degreewise pairing
`⟨-, -⟩_i : H^i_c(X, K) × H^{2d-i}(X, K^∨(d)) ⟶ Λ` satisfies `⟨F_{c,K} x, F_{K^∨(d)} y⟩_i =
⟨x, y⟩_i`, and the untwisted, line-valued pairing
`H^i_c(X, K) × H^{2d-i}(X, K^∨) ⟶ Λ(-d)` satisfies
`⟨F_{c,K} x, F_{K^∨} y⟩^{untw}_i = q^d ⟨x, y⟩^{untw}_i`.

**(b) Reciprocity.** Over a field, if the line-valued pairing is perfect, `F_{K^∨}` is
conjugate to `q^d (F_{c,K}^{-1})^t`, so the eigenvalues of `F` on `H^{2d-i}(X, K^∨)` are the
`q^d / α` for the eigenvalues `α` of `F` on `H^i_c(X, K)`, with multiplicities.

The pairings are defined in
`WeilConjectures.EtaleCohomology.PoincareDuality.Frobenius.Pairings`, (a) is proved in
`...Frobenius.Equivariance` and (b) in `...Frobenius.Reciprocity`; this module imports all of
them.

## Main definitions

- `AlgebraicGeometry.Etale.TateOrientation.degreewisePoincarePairing`
  (`corollary-degreewise-duality-over-fields--1`): `⟨-, -⟩_i`.
- `AlgebraicGeometry.Etale.TateOrientation.untwistedPoincarePairing`,
  `AlgebraicGeometry.Etale.TateOrientation.untwistedDegreewisePoincarePairing`
  (`corollary-degreewise-duality-over-fields--1`): the untwisted pairing
  `Ra_! K ⊗ᴸ (Ra_* K^∨)[2d] ⟶ Λ_Y(-d)` and its degreewise form.

## Main statements

- `AlgebraicGeometry.Etale.TateOrientation.isWeilPairing_poincarePairing`,
  `AlgebraicGeometry.Etale.TateOrientation.degreewisePoincarePairing_frobeniusOperator`
  (`theorem-poincare-duality-frobenius` (a)): `β_K` is a morphism of Weil objects, and the
  degreewise pairing is Frobenius invariant.
- `AlgebraicGeometry.Etale.TateOrientation.untwistedDegreewisePoincarePairing_frobeniusOperator`
  (`theorem-poincare-duality-frobenius--4`): the untwisted similitude with factor `q^d`.
- `AlgebraicGeometry.Etale.TateOrientation.conj_frobeniusOperator_eq_smul_inverse_dualMap`,
  `AlgebraicGeometry.Etale.TateOrientation.roots_map_charpoly_frobeniusOperator`
  (`theorem-poincare-duality-frobenius--6`, `theorem-poincare-duality-frobenius` (b)): conjugacy and
  reciprocal eigenvalues.

## Implementation notes

The Tate twist `Λ(d)` is a datum (`AlgebraicGeometry.Etale.HasTateTwist`) and the orientation
`γ` is arbitrary, so the Frobenius structures on the twists and the Frobenius equivariance of
the smooth trace (`proposition-purity-trace-commute-frobenius`) are hypotheses: a Weil datum
`τ` on `Λ_X(d)` for which the smooth trace is a morphism of Weil objects, and a Weil datum on
`Λ_Y(-d)` on whose sections Frobenius acts by `q^d`
(`prose-10-21`). The contragredient datum on `K^∨` (resp. `K^∨(d)`) is
characterised by the Frobenius equivariance of the evaluation `K ⊗ᴸ K^∨ ⟶ Λ_X` (resp. of the
twisted evaluation `K ⊗ᴸ K^∨(d) ⟶ Λ_X(d)`), which determines it when `K` is dualizable.

The second factor `H^{2d-i}(X, K^∨(d))` is read as `Hom(Λ_Y, (Ra_* K^∨(d))[j])` with
`i + j = 2d`, and the degreewise pairing passes through
`(Ra_* K^∨(d))[j] ≅ ((Ra_* K^∨(d))[2d])[j - 2d]`, the shift convention of
`corollary-degreewise-duality-over-fields--1`.

The reciprocity statement assumes the line-valued pairing perfect after a trivialisation
`Hom(Λ_Y, Λ_Y(-d)) ≃ Λ` of the value line; at a field stage this is
`corollary-degreewise-duality-over-fields--1`. Over `𝒪_E` it fails (the blueprint's example
`K = [𝒪_E --ϖ--> 𝒪_E]` over a point), which is why (b) is stated over a field.
-/
