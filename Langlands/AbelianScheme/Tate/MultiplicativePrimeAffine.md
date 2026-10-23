# Affine and rational prime-adic comparisons for the multiplicative group

This module extends the published prime-adic comparison between actual torsion
sections of `Gm` and the roots-of-unity Tate twist. It identifies the twist over
an affine test scheme with the twist of its coordinate ring, and extends the
integral comparisons from `ℤ_[p]` to `ℚ_[p]`. All declarations are in
`Langlands.GroupScheme.Gm.TateComparison`.

## Internal provenance

The construction is an internal consequence of the published
`Langlands.AbelianScheme.Tate.MultiplicativePrime` comparison, the ring-induced
twist maps and equivalences in `Langlands.AbelianScheme.Tate.Twist`, and
Mathlib's canonical `Scheme.ΓSpecIso` and `LinearEquiv.baseChange`.
The paired Markdown of the published modules records their original provenance.
No new assertion from original literature is made here. The coordinate-ring
identification is the same canonical ring isomorphism used by the published
`Gm.affinePointsEquiv` and `mu.affinePointsEquiv`.

## Rational comparison on an arbitrary test scheme

Fix a scheme `S`, `T : Over S`, and a prime natural number `p`, expressed by
`Fact p.Prime`. The construction

```text
primeRationalEquiv T p :
  Tate.PrimeAdic.Rational (Gm S).toGrp T p ≃ₗ[ℚ_[p]]
    TateTwist.Rational Γ(T.left, ⊤) p
```

is `primeIntegralEquiv T p` extended from `ℤ_[p]` to `ℚ_[p]`. Both existing
rational modules are precisely the corresponding tensors
`ℚ_[p] ⊗[ℤ_[p]] Integral`; no comparison is assumed as data.
`primeRationalEquiv_tmul` sends `a ⊗ x` to
`a ⊗ primeIntegralEquiv T p x`, and
`primeRationalEquiv_symm_tmul` gives the analogous formula using the inverse
integral equivalence. Both proofs are reflexive for the tensor constructions.

## Affine integral comparison

For `R : CommRingCat` in the same universe as `S` and `f : Spec R ⟶ S`,
`affinePrimeIntegralEquiv p f` is the composite

```text
Tate.PrimeAdic.Integral (Gm S).toGrp (Over.mk f) p
  ≃ₗ[ℤ_[p]] TateTwist.Integral Γ(Spec R, ⊤) p
  ≃ₗ[ℤ_[p]] TateTwist.Integral R p.
```

The first arrow is `primeIntegralEquiv`; the second is `TateTwist.mapEquiv`
for `(Scheme.ΓSpecIso R).commRingCatIsoToRingEquiv`. The forward formula in
`affinePrimeIntegralEquiv_apply` first applies the global-section comparison,
then the twist map induced by `(Scheme.ΓSpecIso R).hom.hom`.
`affinePrimeIntegralEquiv_symm_apply` applies the inverse ring-induced twist
map, then the inverse global-section comparison. These formulas are reflexive.

At coordinate `n`, `evaluation_affinePrimeIntegralEquiv` first applies
`levelEquiv (Over.mk f) (p ^ n)` to the actual torsion coordinate and then
applies `TateTwist.levelMap` for the canonical global-section ring homomorphism.
This is a definitional identity. Thus the construction retains the actual
roots of unity in `R`, without choosing a primitive root or a basis.

The forward and inverse continuity theorems compose the corresponding
continuity proofs for the published prime-integral comparison with
`TateTwist.continuous_map` for the canonical ring homomorphism and its inverse.
`affinePrimeIntegralContinuousLinearEquiv` bundles these proofs with the
integral linear equivalence. Its `_apply` theorem is reflexive.
The topologies are the existing product-subtype inverse-limit topologies,
whose finite-level factors are discrete; no topology on `R` is assumed.

## Affine rational comparison

`affinePrimeRationalEquiv p f` extends `affinePrimeIntegralEquiv p f` from
`ℤ_[p]` to `ℚ_[p]`. Its source is the existing actual rational Tate module
on `Over.mk f`, and its target is `TateTwist.Rational R p`.
The `_tmul` and `_symm_tmul` theorems give the forward and inverse pure-tensor
formulas, both by reflexivity.

`affinePrimeRationalEquiv_apply` states that this map is also the composite
of `primeRationalEquiv (Over.mk f) p` with the existing
`TateTwist.rationalMap` for `(Scheme.ΓSpecIso R).hom.hom`.
The proof uses `LinearEquiv.baseChange_trans` and then definitional equality.
Consequently the rational comparison agrees with affine specialization.

## Scope

The constructions require only the stated schemes, affine test morphism where
applicable, and primality of `p`. They use the actual multiplicative-group
torsion and roots-of-unity limits. They assume no characteristic, invertibility
of `p`, finite étaleness, torsion finiteness, or rank condition. The rational
comparisons are algebraic linear equivalences; no rational topology or
continuity is asserted. This unit does not construct test-scheme restriction
maps, full or away rational comparisons, monodromy, a Weil pairing, a twist
trivialization, or the complete abelian-scheme PEL specialization.
