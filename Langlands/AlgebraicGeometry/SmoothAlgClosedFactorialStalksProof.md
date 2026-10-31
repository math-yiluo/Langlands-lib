# Factorial stalks of smooth schemes over algebraically closed fields

This module proves the published Library proposition
`Langlands.AlgebraicGeometry.SmoothAlgClosedFactorialStalks` with the exact interface

```lean
theorem Langlands.AlgebraicGeometry.smoothAlgClosedFactorialStalks.{u} :
    Langlands.AlgebraicGeometry.SmoothAlgClosedFactorialStalks.{u}
```

For every algebraically closed field `K : Type u`, scheme `X : Scheme.{u}` and smooth morphism
`p : X ⟶ Spec (CommRingCat.of K)`, every stalk `X.presheaf.stalk x` is a
`UniqueFactorizationMonoid`. Mathlib's class extends `IsCancelMulZero`, so the stalk, a
nontrivial local ring, is a domain in which every nonzero nonunit factors uniquely into
irreducibles. The closing theorem has no outer hypotheses.

## Overall route

1. **Power series.** `K⟦X_1, ..., X_n⟧` is factorial
   (`Langlands.CommutativeAlgebra.MvPowerSeriesFactorial`, with the coordinate change of
   `Langlands.CommutativeAlgebra.MvPowerSeriesCoordinateChange`).
2. **Completion.** Let `R` be a Noetherian local `K`-algebra, formally smooth over `K`, with
   residue field reached by `K`. Its `𝔪`-adic completion is isomorphic to some
   `K⟦X_1, ..., X_n⟧` (`Langlands.CommutativeAlgebra.FormallySmoothLocalCompletion`).
3. **Descent.** Factoriality descends along the flat local completion map
   (`Langlands.CommutativeAlgebra.FlatLocalFactorialDescent`).
4. **Localizations.** Every prime localization of a smooth `K`-algebra is factorial: closed
   points by steps 1–3, other primes as localizations of closed-point localizations
   (`Langlands.CommutativeAlgebra.SmoothAlgClosedFactorialLocalizations`).
5. **Schemes.** Every stalk is a prime localization of the section ring of an affine chart
   (this module).

Each helper module has its own Markdown with the details.

## Reduction to rings

`smoothAlgClosedFactorialStalks_of_localizations` takes as hypothesis that every prime
localization of a smooth algebra over an algebraically closed field in universe `u` is
factorial. It follows the affine-chart argument of the published
`Langlands.AlgebraicGeometry.SmoothDomainStalksProof`. Given a point `x`,
`X.affineCover.exists_eq` supplies an affine chart `U` and a point `y` over `x`. The chart map
is an open immersion, so its composite `q` with `p` is smooth.

Composing the inverse of `Scheme.ΓSpecIso` with `q.appTop` gives a ring map
`K → Γ(U, ⊤)`. It is smooth by `RingHom.Smooth.comp`, `RingHom.Smooth.of_bijective` and
`HasRingHomProperty.appTop`. After `algebraize`, `RingHom.smooth_algebraMap` makes `Γ(U, ⊤)` a
smooth `K`-algebra. The point `y` corresponds to a prime `P` of `Γ(U, ⊤)`, and the hypothesis
gives factoriality of `Localization.AtPrime P`. `IsAffineOpen.isLocalization_stalk`
identifies the chart stalk at `y` with a localization at `P.primeCompl`. The canonical
`IsLocalization.algEquiv` and `MulEquiv.uniqueFactorizationMonoid` transfer factoriality to
the chart stalk. The stalk-map isomorphism of the open immersion transfers it to
`X.presheaf.stalk x`.

## Discharging the ring hypothesis

`smoothAlgClosedFactorialStalks_of_mvPowerSeries` takes factoriality of every
`MvPowerSeries (Fin n) K` as its hypothesis. It applies
`uniqueFactorizationMonoid_localization_of_smooth`, and supplies that theorem's completion
hypothesis with `FormallySmoothLocalCompletion.exists_algEquiv_mvPowerSeries`, converting the
`K`-algebra isomorphism to a ring isomorphism.

The closing theorem `smoothAlgClosedFactorialStalks` supplies the power-series hypothesis
with `MvPowerSeriesFactorial.uniqueFactorizationMonoid_of_coord`. That theorem takes the
coordinate change `MvPowerSeriesFactorial.exists_algEquiv_coeff_single_zero_ne_zero` as its
hypothesis. Nothing is left as an outer assumption.

## Provenance and contributions

The statement's Markdown records the original derivation: Stacks Lemma 33.25.3 (Tag 056S,
smooth over a field implies regular) with Lemma 15.123.2 (Tag 0AG0, a regular local ring is
a UFD). The
implemented proof avoids regularity and dimension theory. It instead uses the Cohen-type
identification of the completion via formal smoothness, factoriality of power series rings
via Weierstrass preparation, and faithfully flat descent. The scheme reduction adapts the
published `SmoothDomainStalksProof`.

Worker 254 wrote this module, `FlatLocalFactorialDescent`,
`SmoothAlgClosedFactorialLocalizations` and `MvPowerSeriesFactorial`. Worker 1131 wrote
`FormallySmoothLocalCompletion` and `MvPowerSeriesCoordinateChange`.
