# A minimal formally versal Picard hull over a field

Author: Worker 372.

This internal helper module builds, over a field `k`, a formally versal hull of the relative
Picard deformation problem of a line bundle `M` on the residue fibre. The hull ring is a quotient
of a complete local power-series source with exactly `Index f M` variables, one for each basis
vector of the first-order classes. It is a variant of the Library construction in
`Langlands.AlgebraicGeometry.Deformation.ArtinianPolynomialPresentation` and
`Langlands.AlgebraicGeometry.Picard.FiniteTypePicardInitialStage`. Those use a polynomial
presentation with an arbitrary number of variables. Here the number of variables is minimal,
which is what the dimension bound needs.

Inputs: a field `k : Type u`, a scheme `X`, a proper morphism `f : X ⟶ Spec k`, and a line
bundle `M` on `(relativeSpace f).obj (ArtinianTest.residueBase k k)`. From `hullRing` on, `f` is
also assumed flat.

## Declarations

- `Index f M` is `FiniteBasisPicardFamily.Index f M`, that is
  `ULift (Fin (finrank k (ArtinianDualNumberComparison.Classes f M)))`. `test f M` is the split
  square-zero test `k ⊕ k^Index` of `FiniteBasisPicardFamily`.
- `direction i` is the basis vector `inr (Pi.single i 1)` of `test f M`. `polynomialCover` is the
  `k`-algebra map `MvPolynomial (Index f M) k → test f M` sending `X i` to `direction i`.
  `polynomialCover_surjective` proves that it is surjective: an element `(a, w)` is the image of
  `C a + ∑ i, C (w i) * X i`. `polynomialAugmentation` is its composite with the augmentation of
  the test, and `polynomialAugmentation_X` says every variable has residue `0`.
- `localCover`, `ring`, `augmentation`, `completedCover` and `cover` pass to the completed local
  polynomial source `CompletedLocalPolynomialSource.ring (polynomialAugmentation f M)`, with the
  Library extension equivalences `LocalPolynomialArtinianSource.extend` and
  `CompletedLocalPolynomialSource.localMapEquiv`. `cover_polynomialMap` says that `cover`
  restricted to polynomials is `polynomialCover`, so `cover_surjective` holds.
- `stage` is the initial `ArtinianPicardSourceStep.Stage` on this source. Its test is `test f M`,
  its cover is `cover`, and its family is `FiniteBasisPicardFamily.family f M`.
  `postcomp_surjective` is the Library lifting property
  `CompletedLocalPolynomialSource.postcomp_surjective` for this source.
- With `[Flat f]`: `hullRing`, `hullAugmentation`, `hullBundle` and `hullPoint` are the Library
  limit ring, limit augmentation, effective line bundle and residue point of the source tower
  (`ArtinianPicardSourceTower.limitRing`, `ArtinianPicardTowerAlgebraization.effectiveBundle`,
  `residuePoint`) started at `stage f M`. `hullResidueIso` is
  `effectiveResidueIso`. It identifies the residue fibre of `hullBundle` with `M`.
- `isFormallyVersalAt` proves `ArtinianChartVersality.IsFormallyVersalAt f (hullBundle f M)
  (hullPoint f M)`. It applies `ArtinianPrincipalLifting.isFormallyVersalAt_of_ringLifting` to
  two inputs: ring-map lifting for the effective tower bundle
  (`ArtinianPicardTowerRingLifting.exists_ringLift`, using `postcomp_surjective`), and lifting
  along the dual numbers
  (`ArtinianPicardTowerTangentLifting.hasLiftingForAt_dualReduction`, fed by
  `FiniteBasisPicardTangentLifting.hasLiftingForAt`).
- `generator i` is the image in `hullRing` of the `i`-th variable.
  `hullAugmentation_generator` says that it has residue `0`.
- `eq_constant_of_generator`: let `ψ : hullRing →ₐ[k] B` be a map to an Artinian test that is
  compatible with the augmentations and kills every `generator i`. Then `ψ` equals the constant
  map `algebraMap k B ∘ hullAugmentation`. Proof: both maps, composed with the quotient map from
  the completed source, are compatible maps out of the completed source. They have the same
  coordinates (`CompletedLocalPolynomialSource.coordinateEquiv`), namely `0` on every variable.
  So they agree, and `Ideal.Quotient.algHom_ext` finishes.

## Provenance

Internal construction. The underlying idea is the hull of Schlessinger's theory of functors of
Artin rings: a minimal hull is a quotient of a power series ring in `dim t` variables, where `t`
is the tangent space. Here `t` is the first-order classes
`ArtinianDualNumberComparison.Classes f M`. The versality criterion is the one recorded in
`ArtinianPrincipalLifting` (which cites Stacks Lemma 90.13.2). The Lean route only reuses the
Library tower machinery, started from the minimal finite basis presentation.
