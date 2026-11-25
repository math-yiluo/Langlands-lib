/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.AlgebraicGeometry.AdicStratumCompletionUnit
public import WeilConjectures.AlgebraicGeometry.SfbCompletionNormalization
import all WeilConjectures.AlgebraicGeometry.AdicStratumCompletionUnit
import WeilConjectures.Algebra.Homology.SitePerfectModelRestriction
import all WeilConjectures.AlgebraicGeometry.CompletedPullbackAdjunction
import all WeilConjectures.AlgebraicGeometry.ProEtaleOperations
import WeilConjectures.AlgebraicGeometry.SfbOrdinaryImmersionNormalization
import WeilConjectures.AlgebraicGeometry.SfbOrdinarySliceNormalization
import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor

/-! # Comparing the two presentations of local derived restriction

Source: Stacks Tags 00YY, 03D2 and 06YY; Bhatt--Scholze, Lemma 6.5.8.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option synthInstance.maxSize 2048

universe u v

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Scheme

attribute [local instance] comp_preservesFiniteLimits comp_preservesFiniteColimits

attribute [local irreducible] ConstantCompletion.completed ConstantCompletion.derivedPull
  HasDerivedCategory.standard SfbCompletionNormalization.object

private local instance standardDerived {C : Type (u + 1)} [Category.{v} C]
    [Abelian C] : HasDerivedCategory C := HasDerivedCategory.standard C

private local instance modelEquivalence (X : Scheme.{u})
    (R : Sheaf (ProEt.topology X) RingCat.{u + 1}) :
    (proEtaleModuleToModel R).IsEquivalence := by
  exact inferInstanceAs (proEtaleModuleModelEquivalence X R).inverse.IsEquivalence

private local instance modelAdditive (X : Scheme.{u})
    (R : Sheaf (ProEt.topology X) RingCat.{u + 1}) :
    (proEtaleModuleToModel R).Additive := ⟨by intros; ext U x; rfl⟩

private local instance resIsoEquivalence
    {C : Type (u + 1)} [SmallCategory C] {J : GrothendieckTopology C}
    {R S : Sheaf J CommRingCat.{u + 1}} (e : R ≅ S) :
    (ConstantCompletion.res e.inv).IsEquivalence :=
  ConstantCompletion.restrictScalars_equivalence
    ((sheafCompose J (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).mapIso e.symm)

private theorem normalizationExact (X : Scheme.{u})
    (R : Sheaf (ProEt.topology X) CommRingCat.{u + 1})
    (B : Sheaf (proEtaleModelTopology X) CommRingCat.{u + 1})
    (e : (sfbModelRings X).obj R ≅ B) :
    (proEtaleModuleToModel ((adicLisseForget X).obj R) ⋙
        ConstantCompletion.res e.inv).Additive ∧
      PreservesFiniteLimits (proEtaleModuleToModel ((adicLisseForget X).obj R) ⋙
        ConstantCompletion.res e.inv) ∧
      PreservesFiniteColimits (proEtaleModuleToModel ((adicLisseForget X).obj R) ⋙
        ConstantCompletion.res e.inv) := by
  have := modelEquivalence X ((adicLisseForget X).obj R)
  have := modelAdditive X ((adicLisseForget X).obj R)
  have : (ConstantCompletion.res e.inv).IsEquivalence :=
    ConstantCompletion.restrictScalars_equivalence
      ((sheafCompose (proEtaleModelTopology X)
        (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).mapIso e.symm)
  exact ⟨inferInstance, inferInstance, inferInstance⟩

private noncomputable def representativeIso
    {C D : Type*} [Category C] [Category D] [Abelian C] [Abelian D]
    [HasDerivedCategory C] [HasDerivedCategory D]
    (T : C ⥤ D) [T.Additive] [PreservesFiniteLimits T] [PreservesFiniteColimits T]
    (K : DerivedCategory C) :
    T.mapDerivedCategory.obj K ≅ DerivedCategory.Q.obj
      ((T.mapHomologicalComplex (.up ℤ)).obj (DerivedCategory.Q.objPreimage K)) :=
  T.mapDerivedCategory.mapIso (DerivedCategory.Q.objObjPreimageIso K).symm ≪≫
    T.mapDerivedCategoryFactors.app (DerivedCategory.Q.objPreimage K)

private noncomputable def normalizationIso (X : Scheme.{u})
    {A : Type (u + 1)} [CommRing A] (I : Ideal A)
    (K : DerivedCategory (proEtaleRingModules X (adicLisseCompletedRing X I))) :
    let T := proEtaleModuleToModel
      ((adicLisseForget X).obj (adicLisseCompletedRing X I))
    let H := ConstantCompletion.res (SfbCompletionNormalization.coefficients X I).inv
    letI : T.Additive :=
      modelAdditive X ((adicLisseForget X).obj (adicLisseCompletedRing X I))
    letI : T.IsEquivalence :=
      modelEquivalence X ((adicLisseForget X).obj (adicLisseCompletedRing X I))
    letI : H.IsEquivalence :=
      resIsoEquivalence (SfbCompletionNormalization.coefficients X I)
    SfbCompletionNormalization.object X I K ≅ (T ⋙ H).mapDerivedCategory.obj K := by
  dsimp only
  let T := proEtaleModuleToModel
    ((adicLisseForget X).obj (adicLisseCompletedRing X I))
  let H := ConstantCompletion.res (SfbCompletionNormalization.coefficients X I).inv
  have : T.Additive := modelAdditive X _
  have : T.IsEquivalence := modelEquivalence X _
  have : H.IsEquivalence := ConstantCompletion.restrictScalars_equivalence
    ((sheafCompose (proEtaleModelTopology X) (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).mapIso
      (SfbCompletionNormalization.coefficients X I).symm)
  let M := DerivedCategory.Q.obj
    ((T.mapHomologicalComplex (.up ℤ)).obj (DerivedCategory.Q.objPreimage K))
  unfold SfbCompletionNormalization.object
  exact (representativeIso H M).symm ≪≫
    H.mapDerivedCategory.mapIso (representativeIso T K).symm ≪≫
      (Functor.mapDerivedCategoryCompIso T H).app K

private theorem pullDerivedIso
    {C D : Type (u + 1)} [SmallCategory C] [SmallCategory D]
    {J : GrothendieckTopology C} {J' : GrothendieckTopology D}
    {L : Sheaf J (Type (u + 1)) ⥤ Sheaf J' (Type (u + 1))}
    (F : ConstantCompletion.InverseImageData L)
    (V : Sheaf J' (Type (u + 1)) ⥤ Sheaf J (Type (u + 1))) (adj : L ⊣ V)
    [PreservesFiniteLimits L]
    {R : Sheaf J CommRingCat.{u + 1}} {S : Sheaf J' CommRingCat.{u + 1}}
    (c : F.rings.obj R ⟶ S) [IsIso c]
    [PreservesFiniteLimits (ConstantCompletion.pull F c)]
    [PreservesFiniteColimits (ConstantCompletion.pull F c)] :
    Nonempty ((ConstantCompletion.derivedPull F V adj c).functor ≅
      (ConstantCompletion.pull F c).mapDerivedCategory) := by
  let d := ConstantCompletion.derivedPull F V adj c
  have : ∀ P, IsIso (d.comparison.app P) :=
    SfbAdicRestriction.derivedPull_computes F V adj c
  have : IsIso d.comparison := NatIso.isIso_of_isIso_app d.comparison
  exact ⟨(Localization.fullyFaithfulWhiskeringLeft (ConstantCompletion.Q R)
    (HomologicalComplex.quasiIso (ConstantCompletion.Mod R) (.up ℤ))
    (ConstantCompletion.D S)).preimageIso
      (asIso d.comparison ≪≫ (ConstantCompletion.pull F c).mapDerivedCategoryFactors.symm)⟩

private theorem pullExact
    {C D : Type (u + 1)} [SmallCategory C] [SmallCategory D]
    {J : GrothendieckTopology C} {J' : GrothendieckTopology D}
    {L : Sheaf J (Type (u + 1)) ⥤ Sheaf J' (Type (u + 1))}
    (F : ConstantCompletion.InverseImageData L)
    (V : Sheaf J' (Type (u + 1)) ⥤ Sheaf J (Type (u + 1))) (adj : L ⊣ V)
    [PreservesFiniteLimits L]
    {R : Sheaf J CommRingCat.{u + 1}} {S : Sheaf J' CommRingCat.{u + 1}}
    (c : F.rings.obj R ⟶ S) [IsIso c] :
    PreservesFiniteLimits (ConstantCompletion.pull F c) ∧
      PreservesFiniteColimits (ConstantCompletion.pull F c) := by
  obtain ⟨G, eG, aM, haM⟩ := ConstantCompletion.module_adjunction_exists V adj F c
  have := aM.leftAdjoint_preservesColimits
  exact ⟨ConstantCompletion.pull_finiteLimits_of_isIso F c, inferInstance⟩

/-- Isomorphisms after the original stratum-and-slice restriction give isomorphisms
between the corresponding normalized restrictions. This concerns arbitrary objects,
without a completeness, covering, stratification or perfectness hypothesis.

Source: Stacks Tags 00YY, 03D2 and 06YY; Bhatt--Scholze, Lemma 6.5.8 and
Remark 6.5.10 (auxiliary; not a blueprint node).

Proof: first compare ordinary module functors. The transported original ring
adjunction unit identifies the coefficient ring produced by F with the transported
original inverse-image ring. Compose the inverse of this identification with the
invertible completed scalar map. Uniqueness of module left adjoints now compares
normalized immersion pullback with the specified original module pullback, followed
by transport and scalar restriction. This target coefficient identification need
not be the canonical completion comparison: only its existence is needed here.
For the slice, Over.postEquiv for AsSmall gives a continuous and cocontinuous
transport. Its module pushforward, with the inverse coefficient map, is additive
and exact. Scalar extension along an isomorphism is scalar restriction along its
inverse, giving the ordinary slice comparison.

Both scalar maps are invertible since immersion inverse image and slice restriction
preserve limits. The existing computation lemma identifies their left-derived
pullbacks with the derived functors of their exact ordinary pullbacks, by cancelling
precomposition with localization. Derive the composite ordinary comparison. The
localization-preimage isomorphisms remove the chosen complex representatives in
normalization and in original slice restriction. Apply the resulting exact derived
slice transport to the given local isomorphism and compose the comparison on K
with the inverse comparison on L. Empty slices and zero coefficient rings require
no additional assumption. -/
theorem sfbNormalizedLocalRestriction_iso
    {X S : Scheme.{u}} (i : S ⟶ X) [IsImmersion i]
    (A : Type (u + 1)) [CommRing A] [IsNoetherianRing A] (I : Ideal A)
    (F : ConstantCompletion.InverseImageData (SfbAdicRestriction.inverse i))
    (U : S.ProEt)
    (K L : DerivedCategory (proEtaleRingModules X (adicLisseCompletedRing X I)))
    (h : Nonempty (sfbLocalRestriction i (adicLisseCompletedRing X I) U K ≅
      sfbLocalRestriction i (adicLisseCompletedRing X I) U L)) :
    Nonempty
      ((SfbAdicRestriction.completedPull F (SfbAdicRestriction.direct i)
          (SfbAdicRestriction.adjunction i) A I ⋙
        SfbAdicRestriction.completedPull
          (SfbAdicRestriction.sliceAlgebra (proEtaleModelTopology S) (AsSmall.up.obj U))
          (SfbAdicRestriction.sliceDirect (proEtaleModelTopology S) (AsSmall.up.obj U))
          (SfbAdicRestriction.sliceAdjunction (proEtaleModelTopology S) (AsSmall.up.obj U))
          A I).obj (SfbCompletionNormalization.object X I K) ≅
        (SfbAdicRestriction.completedPull F (SfbAdicRestriction.direct i)
          (SfbAdicRestriction.adjunction i) A I ⋙
        SfbAdicRestriction.completedPull
          (SfbAdicRestriction.sliceAlgebra (proEtaleModelTopology S) (AsSmall.up.obj U))
          (SfbAdicRestriction.sliceDirect (proEtaleModelTopology S) (AsSmall.up.obj U))
          (SfbAdicRestriction.sliceAdjunction (proEtaleModelTopology S) (AsSmall.up.obj U))
          A I).obj (SfbCompletionNormalization.object X I L)) := by
  let J := proEtaleModelTopology S
  let W := AsSmall.up.obj U
  let FS := SfbAdicRestriction.sliceAlgebra J W
  let VS := SfbAdicRestriction.sliceDirect J W
  let aS := SfbAdicRestriction.sliceAdjunction J W
  let RX := adicLisseCompletedRing X I
  let RS := (proEtaleSheafInverseImage i CommRingCat.{u + 1}).obj RX
  let BX := ConstantCompletion.completed (proEtaleModelTopology X) A I
  let BS := ConstantCompletion.completed J A I
  let BT := ConstantCompletion.completed (J.over W) A I
  let cX := ConstantCompletion.completedMap F A I
  let cS := ConstantCompletion.completedMap FS A I
  have := SfbAdicRestriction.inverse_limits i
  have : IsIso cX := SfbAdicRestriction.completedMap_isIso F A I
  have : IsIso cS := SfbAdicRestriction.completedMap_isIso FS A I
  let TX := proEtaleModuleToModel ((adicLisseForget X).obj RX) ⋙
    ConstantCompletion.res (SfbCompletionNormalization.coefficients X I).inv
  let P := proEtaleRingModulePullback i RX RS (Iso.refl _)
  let O := SheafOfModules.overFunctor ((adicLisseForget S).obj RS) U
  let P₁ := ConstantCompletion.pull F cX
  let P₂ := ConstantCompletion.pull FS cS
  obtain ⟨eS, ⟨e₁⟩⟩ := sfbOrdinaryImmersionNormalization i F RX BX BS
    (SfbCompletionNormalization.coefficients X I) cX
  let TS := proEtaleModuleToModel ((adicLisseForget S).obj RS) ⋙
    ConstantCompletion.res eS.inv
  obtain ⟨G, hGa, hGl, hGc, ⟨e₂⟩⟩ :=
    sfbOrdinarySliceNormalization S U RS BS BT eS cS
  have := hGa
  have := hGl
  have := hGc
  obtain ⟨hTXa, hTXl, hTXc⟩ := normalizationExact X RX BX
    (SfbCompletionNormalization.coefficients X I)
  have : TX.Additive := hTXa
  have : PreservesFiniteLimits TX := hTXl
  have : PreservesFiniteColimits TX := hTXc
  obtain ⟨hTSa, hTSl, hTSc⟩ := normalizationExact S RS BS eS
  have : TS.Additive := hTSa
  have : PreservesFiniteLimits TS := hTSl
  have : PreservesFiniteColimits TS := hTSc
  have : O.Additive := ⟨by intros; ext V x; rfl⟩
  have : PreservesFiniteLimits O := (SheafOfModules.overFunctor_exact_ofUniverses _ U).1
  have : PreservesFiniteColimits O := (SheafOfModules.overFunctor_exact_ofUniverses _ U).2
  have : PreservesFiniteLimits P₁ := (pullExact F _ (SfbAdicRestriction.adjunction i) cX).1
  have : PreservesFiniteColimits P₁ := (pullExact F _ (SfbAdicRestriction.adjunction i) cX).2
  have : PreservesFiniteLimits P₂ := (pullExact FS VS aS cS).1
  have : PreservesFiniteColimits P₂ := (pullExact FS VS aS cS).2
  let e : (TX ⋙ P₁) ⋙ P₂ ≅ (P ⋙ O) ⋙ G :=
    Functor.isoWhiskerRight e₁ P₂ ≪≫ Functor.associator P TS P₂ ≪≫
      Functor.isoWhiskerLeft P e₂ ≪≫ (Functor.associator P O G).symm
  let eD : (TX.mapDerivedCategory ⋙ P₁.mapDerivedCategory) ⋙ P₂.mapDerivedCategory ≅
      (P.mapDerivedCategory ⋙ O.mapDerivedCategory) ⋙ G.mapDerivedCategory :=
    Functor.isoWhiskerRight (Functor.mapDerivedCategoryCompIso TX P₁) _ ≪≫
      Functor.mapDerivedCategoryCompIso (TX ⋙ P₁) P₂ ≪≫
      Functor.mapDerivedCategoryNatIso e ≪≫ (Functor.mapDerivedCategoryCompIso (P ⋙ O) G).symm ≪≫
      Functor.isoWhiskerRight (Functor.mapDerivedCategoryCompIso P O).symm _
  obtain ⟨d₁⟩ := pullDerivedIso F (SfbAdicRestriction.direct i)
    (SfbAdicRestriction.adjunction i) cX
  obtain ⟨d₂⟩ := pullDerivedIso FS VS aS cS
  let H₁ := SfbAdicRestriction.completedPull F (SfbAdicRestriction.direct i)
    (SfbAdicRestriction.adjunction i) A I
  let H₂ := SfbAdicRestriction.completedPull FS VS aS A I
  let comparison (M : DerivedCategory (proEtaleRingModules X RX)) :
      (H₁ ⋙ H₂).obj (SfbCompletionNormalization.object X I M) ≅
        G.mapDerivedCategory.obj (sfbLocalRestriction i RX U M) :=
    H₂.mapIso (H₁.mapIso (normalizationIso X I M) ≪≫
        d₁.app (TX.mapDerivedCategory.obj M)) ≪≫
      d₂.app (P₁.mapDerivedCategory.obj (TX.mapDerivedCategory.obj M)) ≪≫
      eD.app M ≪≫ G.mapDerivedCategory.mapIso (representativeIso O _)
  obtain ⟨h⟩ := h
  exact ⟨comparison K ≪≫ G.mapDerivedCategory.mapIso h ≪≫ (comparison L).symm⟩

end AlgebraicGeometry.Scheme
