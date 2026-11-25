# Finite-type smooth-family representers from a Picard scheme and dual geometry

Module
`Langlands.AlgebraicGeometry.Picard.FiniteTypeSmoothFamilyAbelianRepresentabilityAssembly`.
It is the final assembly of the proof of
`Langlands.AbelianScheme.FiniteTypeSmoothFamilyAbelianRepresentabilityStatement.{u}`.
The module proves conditional theorems and adds no axioms. Its general theorem
has two premises, both published statements:

- `Langlands.AlgebraicGeometry.Picard.FiniteTypeAbelianPicardSheafSchemeStatement`
  (over a finite-type `ℤ`-algebra `R`, the fppf Picard class sheaf of every
  abelian scheme over `Spec R` is represented by a scheme);
- `Langlands.AbelianScheme.FiniteTypeDualSchemeGeometryStatement`
  (over such `R`, the chosen dual parameter of every abelian scheme with
  `HasDualScheme` is smooth, proper and geometrically connected).

The module does not prove the first premise. The second premise is discharged
in the last theorem by the Library's unconditional proof
`finiteTypeDualSchemeGeometry` of `FiniteTypeDualSchemeGeometryStatement`, from
module `Langlands.AlgebraicGeometry.Picard.FiniteTypeDualSchemeGeometryProof`.
The smooth-family comparison is not a premise. The module uses the Library's
unconditional proof `smoothFamilyPicardZeroComparison` of
`SmoothFamilyPicardZeroComparisonStatement`, from module
`Langlands.AlgebraicGeometry.Picard.SmoothFamilyPicardZeroComparisonProof`.

## Declarations

All declarations are in namespace `Langlands.AbelianScheme`.

- `relativeProjection_app_isIso_of_abelian` (private). For an abelian scheme
  `A` over `S`, every projection `T ×_S A → T` induces isomorphisms on sections
  over every open of `T`. This is the published
  `smoothProperConnectedGlobalFunctions` applied to the base-changed structure
  morphism `pullback.fst T.hom A.X.hom`. That morphism is smooth, proper and
  geometrically connected by instances.
- `toClassPicardSheaf_isIso`. The canonical map
  `RigidifiedLineBundle.toClassPicardSheaf A.X.hom (unitSection A) _` is an
  isomorphism. It goes from the rigidified class presheaf to
  `RelativePicard.classSheafPresheaf A.X.hom`. The proof applies the published
  `rigidifiedFppfComparison` (`A.X.hom` is quasi-compact and quasi-separated,
  since it is proper). That shows `toPicardSheaf` is an isomorphism. The proof
  then composes with the isomorphism `forgetSheafIso`, using
  `toPicardSheaf_forgetSheafIso_hom`.
- `exists_isUniversal_of_classSheafPresheaf_representableBy`. A representation
  `r` of `classSheafPresheaf A.X.hom` by `P` is transported along the inverse
  of that isomorphism, using `Functor.RepresentableBy.ofIso`. This gives a
  representation of the rigidified class presheaf. The published
  `RigidifiedLineBundle.representationUniversalBundle` then gives an actual
  `L : RigidifiedFamily A P` with
  `RigidifiedLineBundle.IsUniversal A.X.hom (unitSection A) _ L`.
- `hasDualScheme_of_finiteTypeAbelianPicardSheafScheme`. Assume
  `FiniteTypeAbelianPicardSheafSchemeStatement`. For every `R` of finite type
  over `ℤ` and every `A` over `Spec R`, it gives a representing `P` and hence a
  universal `L`. The published `finiteTypePicardZeroOpenLocus` gives an open
  `U` with `IsPicardZeroOpenLocus A L U`, and
  `hasDualScheme_of_isPicardZeroOpenLocus` gives `HasDualScheme A`.
- `finiteTypeSmoothFamilyAbelianRepresentability_of_prerequisites`.

  ```lean
  theorem finiteTypeSmoothFamilyAbelianRepresentability_of_prerequisites
      (picard : FiniteTypeAbelianPicardSheafSchemeStatement.{u})
      (geometry : FiniteTypeDualSchemeGeometryStatement.{u}) :
      FiniteTypeSmoothFamilyAbelianRepresentabilityStatement.{u}
  ```

  For given `R` and `A`, the proof takes `hA : HasDualScheme A` from the
  previous theorem and `geometry R A hA : DualSchemeGeometry A hA`. It then
  applies `exists_isUniversalSmoothFamilyOnQuasiSeparatedTests_of_hasDualScheme`
  from the companion module
  `Langlands.AlgebraicGeometry.Picard.SmoothFamilyUniversalOfPicardZeroUniversal`,
  with the published `smoothFamilyPicardZeroComparison` as its comparison
  argument. This gives an actual abelian scheme `B` over `Spec R` and an actual
  rigidified family `L` on `B.X` with
  `IsUniversalSmoothFamilyOnQuasiSeparatedTests A L`, which is the target's
  conclusion for `A`.
- `finiteTypeSmoothFamilyAbelianRepresentability_of_picardSheafScheme`.

  ```lean
  theorem finiteTypeSmoothFamilyAbelianRepresentability_of_picardSheafScheme
      (picard : FiniteTypeAbelianPicardSheafSchemeStatement.{u}) :
      FiniteTypeSmoothFamilyAbelianRepresentabilityStatement.{u}
  ```

  This is the previous theorem with its geometry argument supplied by the
  published `finiteTypeDualSchemeGeometry.{u}`. Its only premise is scheme
  representability of the Picard sheaf.

## Use in the proof

This module does not import a proof of the premise
`FiniteTypeAbelianPicardSheafSchemeStatement`. The Library proves it as
`Langlands.AlgebraicGeometry.Picard.finiteTypeAbelianPicardSheafScheme`, in
module `Langlands.AlgebraicGeometry.Picard.FiniteTypeAbelianPicardSheafSchemeProof`.
The companion module
[`FiniteTypeSmoothFamilyAbelianRepresentabilityProof`](FiniteTypeSmoothFamilyAbelianRepresentabilityProof.md)
proves `FiniteTypeSmoothFamilyAbelianRepresentabilityStatement` by applying
`finiteTypeSmoothFamilyAbelianRepresentability_of_picardSheafScheme` to that
theorem.

The Library's smooth-family condition is an explicit geometric-fibre witness
condition. Its relation to Picard-zero (translation-invariant) classes is the
content of the published comparison theorem used above.
