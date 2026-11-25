/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.AlgebraicGeometry.AdicImmersionCompletedModel
public import WeilConjectures.AlgebraicGeometry.AdicResidueLiftComparisons
import WeilConjectures.AlgebraicGeometry.AdicImmersionConstantModuleComparison
import all WeilConjectures.AlgebraicGeometry.AdicStratumCompletionUnit
import all WeilConjectures.AlgebraicGeometry.ProEtaleOperations
import WeilConjectures.CategoryTheory.LocalizedModuleExactForSystems
import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor

/-! # Slice comparisons for the fixed completed immersion model

Source: Bhatt--Scholze, Proposition 6.6.11, forward implication;
Lemma 6.5.8 and Remark 6.5.10. Stacks Project, Tags 03A0, 03CY, 099L and 099R.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option synthInstance.maxSize 2048

attribute [local instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Scheme

private local instance (priority := 50000) modelSheafify (S : Scheme.{u}) :
    HasSheafify (proEtaleModelTopology S) AddCommGrpCat.{u + 1} :=
  SheafOfModules.hasSheafify_coefficientUniverse.{u + 1, u + 1, u + 1}

private local instance (priority := 50000) modelLocallyBijective (S : Scheme.{u}) :
    (proEtaleModelTopology S).WEqualsLocallyBijective AddCommGrpCat.{u + 1} :=
  SheafOfModules.wEqualsLocallyBijective_coefficientUniverse.{u + 1, u + 1, u + 1}

private local instance (priority := 50000) fixedSheafify (X : Scheme.{u}) :
    HasSheafify (ProEt.topology X) AddCommGrpCat.{u + 1} :=
  SheafOfModules.hasSheafify_coefficientUniverse.{u + 1, u, u + 1}

private local instance fixedLocallyBijective (S : Scheme.{u}) :
    (ProEt.topology S).WEqualsLocallyBijective AddCommGrpCat.{u + 1} :=
  SheafOfModules.wEqualsLocallyBijective_coefficientUniverse.{u + 1, u, u + 1}

private noncomputable local instance fixedAbelian (X : Scheme.{u})
    (R : Sheaf (ProEt.topology X) CommRingCat.{u + 1}) :
    Abelian (proEtaleRingModules X R) :=
  SheafOfModules.instAbelian.{u + 1, u, u + 1, u + 1} _

private local instance (priority := 40000) modelAbelian (S : Scheme.{u})
    (R : Sheaf (proEtaleModelTopology S) CommRingCat.{u + 1}) :
    Abelian (ConstantCompletion.Mod R) :=
  SheafOfModules.instAbelian.{u + 1, u + 1, u + 1, u + 1} _

attribute [local instance 40000] fixedAbelian

attribute [local instance 30000] proEtaleRingModules_hasDerivedCategory

private local instance standardDerived {C : Type*} [Category C] [Abelian C] :
    HasDerivedCategory C := HasDerivedCategory.standard C

private def realizeExact
    {C D : Type*} [Category C] [Category D] [Abelian C] [Abelian D]
    [HasDerivedCategory C] [HasDerivedCategory D]
    (F : C ⥤ D) [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    (K : DerivedCategory C) :
    DerivedCategory.Q.obj
        ((F.mapHomologicalComplex (.up ℤ)).obj (DerivedCategory.Q.objPreimage K)) ≅
      F.mapDerivedCategory.obj K :=
  (F.mapDerivedCategoryFactors.app (DerivedCategory.Q.objPreimage K)).symm ≪≫
    F.mapDerivedCategory.mapIso (DerivedCategory.Q.objObjPreimageIso K)

private def normalizationIso (X : Scheme.{u})
    {A : Type (u + 1)} [CommRing A] (I : Ideal A)
    (K : DerivedCategory (proEtaleRingModules X (adicLisseCompletedRing X I))) :
    SfbCompletionNormalization.object X I K ≅
      (sfbImmersionNormalizeModules X I).mapDerivedCategory.obj K := by
  let R := (adicLisseForget X).obj (adicLisseCompletedRing X I)
  let F := proEtaleModuleToModel R
  let H := ConstantCompletion.res (SfbCompletionNormalization.coefficients X I).inv
  have : F.Additive := ⟨by intros; ext U x; rfl⟩
  have : PreservesFiniteLimits F :=
    inferInstanceAs (PreservesFiniteLimits (proEtaleModuleModelEquivalence X R).inverse)
  have : PreservesFiniteColimits F :=
    inferInstanceAs (PreservesFiniteColimits (proEtaleModuleModelEquivalence X R).inverse)
  have := (siteRestrictScalars_exact (SfbCompletionNormalization.coefficients X I).inv).1
  have := (siteRestrictScalars_exact (SfbCompletionNormalization.coefficients X I).inv).2
  let M := (ConstantCompletion.Q ((sfbModelRings X).obj (adicLisseCompletedRing X I))).obj
    ((F.mapHomologicalComplex (.up ℤ)).obj (DerivedCategory.Q.objPreimage K))
  exact realizeExact H M ≪≫ H.mapDerivedCategory.mapIso (realizeExact F K) ≪≫
    (Functor.mapDerivedCategoryCompIso F H).app K

private def completedModelIso {X S : Scheme.{u}} (i : S ⟶ X) [IsImmersion i]
    {A : Type (u + 1)} [CommRing A] (I : Ideal A)
    (K : DerivedCategory (proEtaleRingModules X (adicLisseCompletedRing X I))) :
    sfbImmersionCompletedModel i I K ≅
      (sfbImmersionCompletedPullModules i I).mapDerivedCategory.obj
        ((sfbImmersionNormalizeModules X I).mapDerivedCategory.obj K) := by
  have := SfbAdicRestriction.inverse_limits i
  have := SfbAdicRestriction.completedMap_isIso (sfbImmersionAlgebra i) A I
  let d := ConstantCompletion.derivedPull (sfbImmersionAlgebra i)
    (SfbAdicRestriction.direct i) (SfbAdicRestriction.adjunction i)
    (ConstantCompletion.completedMap (sfbImmersionAlgebra i) A I)
  let M := SfbCompletionNormalization.object X I K
  have := SfbAdicRestriction.derivedPull_computes (sfbImmersionAlgebra i)
    (SfbAdicRestriction.direct i) (SfbAdicRestriction.adjunction i)
    (ConstantCompletion.completedMap (sfbImmersionAlgebra i) A I)
    (DerivedCategory.Q.objPreimage M)
  exact d.functor.mapIso (DerivedCategory.Q.objObjPreimageIso M).symm ≪≫
    asIso (d.comparison.app (DerivedCategory.Q.objPreimage M)) ≪≫
    realizeExact (sfbImmersionCompletedPullModules i I) M ≪≫
    (sfbImmersionCompletedPullModules i I).mapDerivedCategory.mapIso (normalizationIso X I K)

private theorem completedConstantIso {X S : Scheme.{u}} (i : S ⟶ X) [IsImmersion i]
    {A : Type (u + 1)} [CommRing A] (I : Ideal A)
    (P : CochainComplex (ModuleCat.{u + 1} A) ℤ) :
    Nonempty (sfbImmersionCompletedModel i I (sfbCompletedModel X I P) ≅
      adicResidueConstantPerfect.{u, 0} S I P) := by
  obtain ⟨c⟩ := sfbImmersion_constantModuleComparison i I
  let N := sfbImmersionNormalizeModules X I
  let T := sfbImmersionCompletedPullModules i I
  let C := ((sfbImmersionActualConstants X I).mapHomologicalComplex (.up ℤ)).obj P
  refine ⟨completedModelIso i I (sfbCompletedModel X I P) ≪≫ ?_⟩
  change T.mapDerivedCategory.obj (N.mapDerivedCategory.obj (DerivedCategory.Q.obj C)) ≅ _
  exact T.mapDerivedCategory.mapIso (N.mapDerivedCategoryFactors.app C) ≪≫
    T.mapDerivedCategoryFactors.app ((N.mapHomologicalComplex (.up ℤ)).obj C) ≪≫
    (ConstantCompletion.Q _).mapIso ((NatIso.mapHomologicalComplex c (.up ℤ)).app P)

attribute [-instance] WeilConjectures.integralCoefficientAbSheafify
  WeilConjectures.integralCoefficientAbLocallyBijective in
/-- Slice normalization for the specified completed inverse image, uniformly in the complex.
The same equivalence compares all completed constant models; neither completeness nor a
residue presentation is assumed.

Source: Stacks Tags 03A0, 03CY, 03DJ, 099L and 099R; Bhatt--Scholze, Lemma 6.5.8
(auxiliary; not a blueprint node).
Proof: the AsSmall equivalence induces the equivalence of categories over U and up(U).
The projection-normalized constant-ring comparison identifies inverse image of the
completed ring on X with the completed ring on S: the immersion inverse image preserves
limits, and each finite quotient comparison is invertible. Restrict that ring
isomorphism to the slice. Compose the slice-site module equivalence with scalar
restriction along it, and derive this exact equivalence to obtain eU.
For the first comparison, the same exact module inverse image is used in
sfbImmersionCompletedModel and in proEtaleRingDerivedPullback. Their tensor insertions
agree on generalized sections, so the universal derived comparisons identify their
values. Exact restriction to the slice commutes with both localizations. The unit and
counit comparisons with the selected localization representatives give the displayed
isomorphism, uniformly for every K. For the second comparison, constant inverse image
and AsSmall transport identify the constant A-module functors. The completed coefficient
map is identified by all finite projections. Associativity of scalar extension therefore
identifies its two completed module realizations. Apply this termwise to every A-complex
P, then exact slice restriction and localization. The construction uses the same eU as
in the first comparison. Nothing requires P to be perfect or bounded. Empty U and
zero coefficient rings satisfy the same equivalence and scalar-insertion identities. -/
theorem sfbImmersion_sliceComparisons
    {X S : Scheme.{u}} (i : S ⟶ X) [IsImmersion i]
    {A : Type (u + 1)} [CommRing A] [IsNoetherianRing A] (I : Ideal A) :
    ∀ U : S.ProEt, ∃ eU :
          ConstantCompletion.D
            ((ConstantCompletion.completed (coefficientProEtaleModelTopology.{u, 0} S) A I).over
              ((AsSmall.up : S.ProEt ⥤ coefficientProEtaleSiteModel.{u, 0} S).obj U)) ≌
            (let R := (adicLisseForget S).obj
              ((proEtaleSheafInverseImage i CommRingCat.{u + 1}).obj
                (adicLisseCompletedRing X I))
             @DerivedCategory (SheafOfModules.{u + 1} (R.over U)) _ _
               (HasDerivedCategory.standard _)),
        (∀ K : @DerivedCategory (proEtaleRingModules X (adicLisseCompletedRing X I)) _ _
            (proEtaleRingModules_hasDerivedCategory X (adicLisseCompletedRing X I)),
          Nonempty (sfbLocalRestriction i (adicLisseCompletedRing X I) U K ≅
          eU.functor.obj ((adicResidueRestriction.{u + 1}
            (ConstantCompletion.completed (coefficientProEtaleModelTopology.{u, 0} S) A I)
            ((AsSmall.up : S.ProEt ⥤ coefficientProEtaleSiteModel.{u, 0} S).obj U)).obj
              (sfbImmersionCompletedModel i I K)))) ∧
        ∀ P : CochainComplex (ModuleCat.{u + 1} A) ℤ,
          Nonempty (eU.functor.obj ((adicResidueRestriction.{u + 1}
            (ConstantCompletion.completed (coefficientProEtaleModelTopology.{u, 0} S) A I)
            ((AsSmall.up : S.ProEt ⥤ coefficientProEtaleSiteModel.{u, 0} S).obj U)).obj
              (adicResidueConstantPerfect.{u, 0} S I P)) ≅
            sfbLocalRestriction i (adicLisseCompletedRing X I) U (sfbCompletedModel X I P)) := by
  intro U
  let R := (adicLisseForget S).obj
    ((proEtaleSheafInverseImage i CommRingCat.{u + 1}).obj (adicLisseCompletedRing X I))
  let B := ConstantCompletion.completed (proEtaleModelTopology S) A I
  let V := (AsSmall.up : S.ProEt ⥤ proEtaleSiteModel S).obj U
  let N := sfbImmersionNormalizeModules X I
  let T := sfbImmersionCompletedPullModules i I
  let L := SheafOfModules.overFunctor (siteModuleRings B) V
  let F := proEtaleRingModulePullback i (adicLisseCompletedRing X I)
    ((proEtaleSheafInverseImage i CommRingCat.{u + 1}).obj (adicLisseCompletedRing X I))
    (Iso.refl _)
  let H := SheafOfModules.overFunctor R U
  let RC := (proEtaleSheafInverseImage i CommRingCat.{u + 1}).obj
    (adicLisseCompletedRing X I)
  have : H.Additive := SheafOfModules.localizedSystemRestrictionAdditive.{u + 1, u, 0} RC U
  have : PreservesFiniteLimits H :=
    SheafOfModules.localizedSystemRestrictionLimits.{u + 1, u, 0} RC U
  have : PreservesFiniteColimits H :=
    SheafOfModules.localizedSystemRestrictionColimits.{u + 1, u, 0} RC U
  have : L.Additive := ringedOverFunctor_additive B V
  have : PreservesFiniteLimits L := ringedOverFunctor_preservesFiniteLimits B V
  have : PreservesFiniteColimits L := ringedOverFunctor_preservesFiniteColimits B V
  obtain ⟨e, he, ⟨h⟩⟩ := sfbImmersion_moduleNormalization i I U
  have : e.functor.Additive := he
  let eD := e.mapDerivedCategory
  let chain : (N ⋙ T ⋙ L ⋙ e.functor).mapDerivedCategory ≅
      N.mapDerivedCategory ⋙ T.mapDerivedCategory ⋙ L.mapDerivedCategory ⋙
        eD.functor :=
    (Functor.mapDerivedCategoryCompIso N (T ⋙ L ⋙ e.functor)).symm ≪≫
      Functor.isoWhiskerLeft N.mapDerivedCategory
        ((Functor.mapDerivedCategoryCompIso T (L ⋙ e.functor)).symm) ≪≫
      Functor.isoWhiskerLeft N.mapDerivedCategory
        (Functor.isoWhiskerLeft T.mapDerivedCategory
          ((Functor.mapDerivedCategoryCompIso L e.functor).symm))
  let compare := chain.symm ≪≫ Functor.mapDerivedCategoryNatIso h
  have first (K : DerivedCategory (proEtaleRingModules X (adicLisseCompletedRing X I))) :
      Nonempty (sfbLocalRestriction i (adicLisseCompletedRing X I) U K ≅
        eD.functor.obj ((adicResidueRestriction B V).obj
          (sfbImmersionCompletedModel i I K))) := by
    exact ⟨realizeExact H (F.mapDerivedCategory.obj K) ≪≫
      (Functor.mapDerivedCategoryCompIso F H).app K ≪≫
      compare.symm.app K ≪≫
      eD.functor.mapIso (L.mapDerivedCategory.mapIso (completedModelIso i I K).symm)⟩
  refine ⟨eD, first, ?_⟩
  intro P
  obtain ⟨hP⟩ := first (sfbCompletedModel X I P)
  obtain ⟨cP⟩ := completedConstantIso i I P
  exact ⟨eD.functor.mapIso (L.mapDerivedCategory.mapIso cP.symm) ≪≫ hP.symm⟩

end AlgebraicGeometry.Scheme
