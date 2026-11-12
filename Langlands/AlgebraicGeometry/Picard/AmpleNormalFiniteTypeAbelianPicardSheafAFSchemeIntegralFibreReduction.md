# The projective abelian Picard statement from the general integral-fibre statement

Authors: Worker 227.

## Results

The module proves two theorems in the namespace
`Langlands.AlgebraicGeometry.Picard`, each with the universe parameter `u`.

```lean
theorem abelianScheme_geometricallyIntegral {S : Scheme.{u}}
    (A : Langlands.AbelianScheme S) :
    GeometricallyIntegral A.X.hom

theorem ampleNormalFiniteTypeAbelianPicardSheafAFScheme_of_noetherianIntegralFibre
    (h : NoetherianIntegralFibrePicardSheafAFSchemeStatement.{u}) :
    AmpleNormalFiniteTypeAbelianPicardSheafAFSchemeStatement.{u}
```

- `abelianScheme_geometricallyIntegral` says that the structure morphism of
  every Library abelian scheme `A` over any scheme `S` is geometrically
  integral (Mathlib's `GeometricallyIntegral`).
- `ampleNormalFiniteTypeAbelianPicardSheafAFScheme_of_noetherianIntegralFibre`
  is conditional. It proves the projective abelian case
  `AmpleNormalFiniteTypeAbelianPicardSheafAFSchemeStatement` (every abelian
  scheme with an ample line bundle over an integrally closed finite-type
  `ℤ`-domain `R` has its fppf Picard class sheaf represented by a scheme in
  which finite sets of points lie in affine opens) from the general
  proposition `NoetherianIntegralFibrePicardSheafAFSchemeStatement` (the same
  conclusion for a proper flat geometrically integral morphism to `Spec R`, `R`
  noetherian, with a section and an ample line bundle). It proves neither
  proposition.

## Proofs

`abelianScheme_geometricallyIntegral`. By Mathlib's
`GeometricallyIntegral.iff_geometricallyIntegral_fiber`, it suffices to show,
for every point `s` of `S`, that the fibre morphism
`A.X.hom.fiberToSpecResidueField s` is geometrically integral. This fibre
morphism is a pullback of `A.X.hom`, so it is smooth and geometrically connected
(`MorphismProperty.pullback_snd` applied to the fields `A.smooth` and
`A.geometricallyConnected` of the abelian scheme). The Library theorem
`Langlands.AbelianScheme.smoothGeometricIntegrality` then says that a smooth,
geometrically connected scheme over a field is geometrically integral. The
option `backward.isDefEq.respectTransparency.types false` is set for this
theorem only, as in the Library's
`RigidifiedClassesEqualizerClosedNoetherianOfSeesawProof`: without it,
instance synthesis fails to find the stability instances
`MorphismProperty.IsStableUnderBaseChangeAlong` for `Smooth` and
`GeometricallyConnected` along `S.fromSpecResidueField s` that
`MorphismProperty.pullback_snd` needs.

`ampleNormalFiniteTypeAbelianPicardSheafAFScheme_of_noetherianIntegralFibre`.
Fix `R` with its instances, an abelian scheme `A` over `Spec R` and the
existence `hL` of an ample line bundle on `A.X.left`. The ring `R` is noetherian
by Mathlib's `Algebra.FiniteType.isNoetherianRing ℤ R`, since `ℤ` is
noetherian. The proof applies `h` to `R`, the scheme `A.X.left` and the
structure morphism `A.X.hom`:

1. properness is the instance `A.proper`, and flatness is found by instance
   search from the smoothness instance `A.smooth` (smooth morphisms are flat);
2. geometric integrality is `abelianScheme_geometricallyIntegral A`;
3. the section is the underlying morphism `(η[A.X]).left` of the unit of the
   group object `A.X` (`open scoped CategoryTheory.MonObj`); its composite with
   `A.X.hom` is the identity because `η[A.X]` is a morphism in
   `Over (Spec R)` out of the monoidal unit, whose structure morphism is the
   identity of `Spec R`; `simp` closes the goal with the simp lemmas
   `Over.w`, `Over.tensorUnit_left` and `Over.tensorUnit_hom`;
4. the ample line bundle is `hL`.

The conclusion of `h` is literally the conclusion of the target proposition.

## Provenance and use

This is an internal reduction. It records that an abelian scheme over `Spec R`
with an ample line bundle satisfies the hypotheses of
`NoetherianIntegralFibrePicardSheafAFSchemeStatement`: Grothendieck's existence
theorem in the form of Kleiman, *The Picard scheme*, Theorem 4.8, extended from
Kleiman's locally noetherian test schemes to all test schemes as derived in the
Markdown of that statement. A proof
of that proposition, with this reduction, proves
`AmpleNormalFiniteTypeAbelianPicardSheafAFSchemeStatement`, the target of task
`6db3b992-b6f6-49fc-adcc-33c09c47782e` (Task 5656).
