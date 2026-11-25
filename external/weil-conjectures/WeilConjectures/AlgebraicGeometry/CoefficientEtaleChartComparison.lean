/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.AlgebraicGeometry.AdicResidueLiftComparisons
public import WeilConjectures.CategoryTheory.CoefficientFixedScalarsLocalModels
public import WeilConjectures.CategoryTheory.CommutativeSiteDerivedConstantModuleFunctor
import WeilConjectures.AlgebraicGeometry.AdicExactComparison
import all WeilConjectures.AlgebraicGeometry.CoefficientComparisonFixedPullback
import WeilConjectures.AlgebraicGeometry.ConstructibleComparisonModuleExact
import all WeilConjectures.CategoryTheory.CoefficientFiniteLocalSystemsPullback
import WeilConjectures.CategoryTheory.DerivedCategory.MapDerivedCategoryMate
import all WeilConjectures.CategoryTheory.SiteModuleSheafConstantRingEquivalence
import Mathlib.CategoryTheory.Limits.Constructions.Over.Basic
import WeilConjectures.Mathlib.CategoryTheory.Sites.ConstantSheafOver

/-! # Pro-etale restriction of a supplied constant etale chart

Source: Stacks Project, Tags 099R, 03DJ and 094G.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
attribute [local instance 30000] SheafOfModules.hasSheafify_coefficientUniverse
  SheafOfModules.wEqualsLocallyBijective_coefficientUniverse
universe u v w
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.Scheme

private instance unitInjective {C : Type w} [SmallCategory C]
    (J : GrothendieckTopology C) (B : Type w) [CommRing B] :
    Presheaf.IsLocallyInjective J (SheafOfModules.constantCoefficientUnit J B) :=
  SheafOfModules.constantCoefficientUnit_isLocallyInjective J B

private instance unitSurjective {C : Type w} [SmallCategory C]
    (J : GrothendieckTopology C) (B : Type w) [CommRing B] :
    Presheaf.IsLocallySurjective J (SheafOfModules.constantCoefficientUnit J B) :=
  SheafOfModules.constantCoefficientUnit_isLocallySurjective J B

private def fixedScalarIso {C : Type w} [SmallCategory C]
    (J : GrothendieckTopology C) (B : Type w) [CommRing B] :
    moduleRestriction J B (SheafOfModules.constantCoefficientRing J B)
        (SheafOfModules.constantCoefficientUnit J B) ≅ coefficientModelFixedScalars J B :=
  NatIso.ofComponents (fun _ ↦ Iso.refl _) (by intros; rfl)

private def fixedConstantIso {C : Type w} [SmallCategory C]
    (J : GrothendieckTopology C) (B : Type w) [CommRing B] :
    commutativeSiteConstantModuleFunctor J B ⋙ coefficientModelFixedScalars J B ≅
      constantSheaf J (ModuleCat.{w} B) :=
  Functor.isoWhiskerLeft (commutativeSiteConstantModuleFunctor J B)
      (fixedScalarIso J B).symm ≪≫
    moduleRestrictionConstantIso J B (SheafOfModules.constantCoefficientRing J B)
      (SheafOfModules.constantCoefficientUnit J B)

private def sliceScalars {C : Type w} [SmallCategory C]
    (J : GrothendieckTopology C) (B : Type w) [CommRing B] (U : C) :
    ConstantCompletion.Mod ((ConstantCompletion.constant J B).over U) ⥤
      Sheaf (J.over U) (ModuleCat.{w} B) :=
  let α := Functor.whiskerLeft (Over.forget U).op
    (SheafOfModules.constantCoefficientUnit J B)
  let : Presheaf.IsLocallyInjective (J.over U) α :=
    Presheaf.isLocallyInjective_whisker (J.over U) J (Over.forget U) _
  let : Presheaf.IsLocallySurjective (J.over U) α :=
    Presheaf.isLocallySurjective_whisker (J.over U) J (Over.forget U) _
  moduleRestriction (J.over U) B ((SheafOfModules.constantCoefficientRing J B).over U) α

private instance sliceScalarsEquivalence {C : Type w} [SmallCategory C]
    (J : GrothendieckTopology C) (B : Type w) [CommRing B] (U : C) :
    (sliceScalars J B U).IsEquivalence := by
  dsimp only [sliceScalars]
  infer_instance

private instance sliceScalarsAdditive {C : Type w} [SmallCategory C]
    (J : GrothendieckTopology C) (B : Type w) [CommRing B] (U : C) :
    (sliceScalars J B U).Additive := by
  constructor
  intro M N f g
  ext V m
  rfl

private def sliceScalarsIso {C : Type w} [SmallCategory C]
    (J : GrothendieckTopology C) (B : Type w) [CommRing B] (U : C) :
    SheafOfModules.overFunctor (SheafOfModules.constantCoefficientRing J B) U ⋙
        sliceScalars J B U ≅
      coefficientModelFixedScalars J B ⋙ J.overPullback (ModuleCat.{w} B) U :=
  NatIso.ofComponents (fun _ ↦ Iso.refl _) (by intros; rfl)

private instance overMapColimits {C : Type w} [SmallCategory C]
    (J : GrothendieckTopology C) (B : Type w) [CommRing B]
    {U V : C} (f : U ⟶ V) :
    PreservesFiniteColimits (J.overMapPullback (ModuleCat.{w} B) f) :=
  ⟨fun _ _ _ ↦ PreservesColimitsOfSize.preservesColimitsOfShape
    (self := Adjunction.leftAdjoint_preservesColimits
      (Functor.sheafAdjunctionCocontinuous (Over.map f) (ModuleCat.{w} B)
        (J.over U) (J.over V)))⟩

private def localFixedPullback
    {C D : Type w} [SmallCategory C] [SmallCategory D]
    [HasFiniteLimits C] [HasFiniteLimits D]
    (J : GrothendieckTopology C) (K : GrothendieckTopology D)
    (G : C ⥤ D) [G.IsContinuous J K] [PreservesFiniteLimits G]
    (B : Type w) [CommRing B] (W : C) {V : D} (f : V ⟶ G.obj W) :
    Sheaf (J.over W) (ModuleCat.{w} B) ⥤ Sheaf (K.over V) (ModuleCat.{w} B) :=
  Functor.sheafPullbackConstruction.sheafPullback (Over.post G)
      (ModuleCat.{w} B) (J.over W) (K.over (G.obj W)) ⋙
    K.overMapPullback (ModuleCat.{w} B) f

private def localFixedSquare
    {C D : Type w} [SmallCategory C] [SmallCategory D]
    [HasFiniteLimits C] [HasFiniteLimits D]
    (J : GrothendieckTopology C) (K : GrothendieckTopology D)
    (G : C ⥤ D) [G.IsContinuous J K] [PreservesFiniteLimits G]
    (B : Type w) [CommRing B] (W : C) {V : D} (f : V ⟶ G.obj W) :
    Functor.sheafPullbackConstruction.sheafPullback G (ModuleCat.{w} B) J K ⋙
        K.overPullback (ModuleCat.{w} B) V ≅
      J.overPullback (ModuleCat.{w} B) W ⋙ localFixedPullback J K G B W f :=
by
  let e : Functor.sheafPullbackConstruction.sheafPullback G (ModuleCat.{w} B) J K ⋙
        K.overPullback (ModuleCat.{w} B) V ≅
      (Functor.sheafPullbackConstruction.sheafPullback G (ModuleCat.{w} B) J K ⋙
        K.overPullback (ModuleCat.{w} B) (G.obj W)) ⋙
          K.overMapPullback (ModuleCat.{w} B) f :=
    NatIso.ofComponents (fun F ↦ (Sheaf.pushforwardOverMapIso
      ((Functor.sheafPullbackConstruction.sheafPullback G
        (ModuleCat.{w} B) J K).obj F) f).symm)
      (by intro F F' φ; ext Z m; rfl)
  exact e ≪≫ Functor.isoWhiskerRight (pullbackOverIso J K G B W)
    (K.overMapPullback (ModuleCat.{w} B) f)

private def localFixedConstant
    {C D : Type w} [SmallCategory C] [SmallCategory D]
    [HasFiniteLimits C] [HasFiniteLimits D]
    (J : GrothendieckTopology C) (K : GrothendieckTopology D)
    (G : C ⥤ D) [G.IsContinuous J K] [PreservesFiniteLimits G]
    (B : Type w) [CommRing B] (W : C) {V : D} (f : V ⟶ G.obj W) :
    constantSheaf (J.over W) (ModuleCat.{w} B) ⋙ localFixedPullback J K G B W f ≅
      constantSheaf (K.over V) (ModuleCat.{w} B) := by
  let H : Over W ⥤ Over (G.obj W) := Over.post G
  have h₁ : IsTerminal (H.obj (Over.mk (𝟙 W))) := by
    change IsTerminal (Over.mk (G.map (𝟙 W)))
    rw [G.map_id]
    exact Over.mkIdTerminal
  let e : constantSheaf (J.over W) (ModuleCat.{w} B) ⋙
        Functor.sheafPullbackConstruction.sheafPullback H (ModuleCat.{w} B)
          (J.over W) (K.over (G.obj W)) ≅
      constantSheaf (K.over (G.obj W)) (ModuleCat.{w} B) :=
    Functor.isoWhiskerLeft (constantSheaf (J.over W) (ModuleCat.{w} B))
        (Functor.sheafPullbackConstruction.sheafPullbackIso H
          (ModuleCat.{w} B) (J.over W) (K.over (G.obj W))).symm ≪≫
      H.constantSheafsheafPullbackIso (ModuleCat.{w} B) (J.over W) (K.over (G.obj W))
        Over.mkIdTerminal h₁
  exact Functor.isoWhiskerRight e (K.overMapPullback (ModuleCat.{w} B) f) ≪≫
    Functor.isoWhiskerLeft (Functor.const _)
      ((Over.map f).pushforwardContinuousSheafificationCompatibility
        (ModuleCat.{w} B) (K.over V) (K.over (G.obj W))).symm

/-- A supplied etale constant chart realizes the comparison on every object over that chart.
Source: Stacks Project, Pro-etale Cohomology, 099R; Modules on Sites, 03DJ;
Cohomology on Sites, 094G.
(auxiliary; not a blueprint node).

Proof: Localize the etale/pro-etale inclusion over W and its image. Slice inverse image
commutes with restriction: both are left adjoint to the direct-image functor given by
precomposition on the corresponding slice sites. Compose with restriction along the
supplied morphism from V. This gives comparison followed by restriction to V as a functor
of the supplied etale restriction. Inverse image preserves constant module sheaves, with
the comparison normalized to the identity on constant scalar sections. Constant-scalar
restriction is an exact equivalence; its natural comparison with comparison inverse image
identifies the intrinsic comparison with adicFinitePullback. The constant module presheaf
and its sheafification identify the other side with commutative constant realization.
Apply this exact composite to hM. The constant comparisons are natural in modules, so
applying them to all terms and differentials gives a cochain isomorphism. Descend to the
standard derived localizations and use their factorization isomorphisms. This proves the
stated literal-slice comparison. No boundedness, finiteness, stalk or covering assumption
is used, and the same formulas include empty charts and zero complexes. -/
theorem coefficient_etale_chart_comparison
    (X : Scheme.{u}) (B : Type (max v (u + 1))) [CommRing B]
    (K : ConstantCompletion.D
      (ConstantCompletion.constant (smallModelComparisonEtaleTopology.{u, v} X) B))
    (W : smallModelComparisonEtaleSite.{u, v} X)
    (M : CochainComplex (ModuleCat.{max v (u + 1)} B) ℤ)
    (hM : CoefficientFixedLocalModel (smallModelComparisonEtaleTopology.{u, v} X) B K W M) :
    letI := HasDerivedCategory.standard (ConstantCompletion.Mod
      (ConstantCompletion.constant (coefficientProEtaleModelTopology.{u, v} X) B))
    ∀ (V : coefficientProEtaleSiteModel.{u, v} X),
      ((AsSmall.down : coefficientProEtaleSiteModel.{u, v} X ⥤ X.ProEt).obj V ⟶
        (toProEt X).obj (AsSmall.down.obj W)) →
      Nonempty ((adicResidueRestriction
        (ConstantCompletion.constant (coefficientProEtaleModelTopology.{u, v} X) B) V).obj
          ((commutativeSiteDerivedConstantModuleFunctor.{max v (u + 1), max v (u + 1),
            max v (u + 1), max v (u + 1) + 1}
            (coefficientProEtaleModelTopology.{u, v} X) B).obj (DerivedCategory.Q.obj M)) ≅
        (adicResidueRestriction
          (ConstantCompletion.constant (coefficientProEtaleModelTopology.{u, v} X) B) V).obj
            ((adicFinitePullback.{u, v} X B).obj K)) := by
  let J := smallModelComparisonEtaleTopology.{u, v} X
  let T := coefficientProEtaleModelTopology.{u, v} X
  let G := smallModelComparisonInclusion.{u, v} X
  let F := coefficientModelFixedScalars J B
  let H := coefficientModelFixedScalars T B
  let P := AlgebraicGeometry.ProEtale.constructibleComparisonPullback.{u, v} X B
  let R := ConstantCompletion.constant J B
  let S := ConstantCompletion.constant T B
  let C := commutativeSiteConstantModuleFunctor T B
  let := HasDerivedCategory.standard (ConstantCompletion.Mod R)
  let := HasDerivedCategory.standard (ConstantCompletion.Mod S)
  have : PreservesFiniteLimits P :=
    (AlgebraicGeometry.ProEtale.constructibleComparisonPullback_exact_faithful X B).1
  have : P.Additive := Functor.additive_of_preserves_binary_products P
  have : PreservesFiniteColimits P := inferInstance
  have (U : smallModelComparisonEtaleSite.{u, v} X) :
      HasSheafify (J.over U) (ModuleCat.{max v (u + 1)} B) :=
    GrothendieckTopology.hasSheafify_of_isGrothendieckAbelian _ _
  have (U : coefficientProEtaleSiteModel.{u, v} X) :
      HasSheafify (T.over U) (ModuleCat.{max v (u + 1)} B) :=
    GrothendieckTopology.hasSheafify_of_isGrothendieckAbelian _ _
  let := HasDerivedCategory.standard (Sheaf J (ModuleCat.{max v (u + 1)} B))
  let := HasDerivedCategory.standard (Sheaf T (ModuleCat.{max v (u + 1)} B))
  let (U : smallModelComparisonEtaleSite.{u, v} X) :
      HasDerivedCategory.{max v (u + 1) + 1}
        (Sheaf (J.over U) (ModuleCat.{max v (u + 1)} B)) := HasDerivedCategory.standard _
  let (U : coefficientProEtaleSiteModel.{u, v} X) :
      HasDerivedCategory.{max v (u + 1) + 1}
        (Sheaf (T.over U) (ModuleCat.{max v (u + 1)} B)) := HasDerivedCategory.standard _
  obtain ⟨eP⟩ := adicExactComparison X B
  let Q := ConstantCompletion.Q R
  let Wq := HomologicalComplex.quasiIso (ConstantCompletion.Mod R) (.up ℤ)
  let U := AlgebraicGeometry.ProEtale.constructibleComparisonComplexPullback X B ⋙
    ConstantCompletion.Q S
  let : Localization.Lifting Q Wq U (adicFinitePullback.{u, v} X B) := ⟨eP⟩
  let : Localization.Lifting Q Wq U P.mapDerivedCategory := ⟨P.mapDerivedCategoryFactors⟩
  let ep : P.mapDerivedCategory ≅ adicFinitePullback.{u, v} X B :=
    Localization.liftNatIso Q Wq U U P.mapDerivedCategory
      (adicFinitePullback.{u, v} X B) (Iso.refl _)
  intro V fac
  let f : V ⟶ G.obj W := AsSmall.up.map fac
  have : HasFiniteLimits (smallModelComparisonEtaleSite.{u, v} X) := inferInstance
  have : HasFiniteLimits (coefficientProEtaleSiteModel.{u, v} X) := inferInstance
  have : PreservesFiniteLimits
      (AsSmall.down : smallModelComparisonEtaleSite.{u, v} X ⥤ X.Etale) :=
    inferInstanceAs (PreservesFiniteLimits
      (AsSmall.equiv.{u, u + 1, max v (u + 1)} (C := X.Etale)).inverse)
  have : PreservesFiniteLimits
      (AsSmall.up : X.ProEt ⥤ coefficientProEtaleSiteModel.{u, v} X) :=
    inferInstanceAs (PreservesFiniteLimits
      (AsSmall.equiv.{u, u + 1, max v (u + 1)} (C := X.ProEt)).functor)
  have : PreservesFiniteLimits G := inferInstance
  let := HasDerivedCategory.standard (Sheaf (J.over W) (ModuleCat.{max v (u + 1)} B))
  let := HasDerivedCategory.standard (Sheaf (T.over V) (ModuleCat.{max v (u + 1)} B))
  let L := localFixedPullback J T G B W f
  let Rp := T.overPullback (ModuleCat.{max v (u + 1)} B) V
  let O : ConstantCompletion.Mod S ⥤ ConstantCompletion.Mod (S.over V) :=
    SheafOfModules.overFunctor.{max v (u + 1)}
      (SheafOfModules.constantCoefficientRing T B) V
  let E := sliceScalars T B V
  let := HasDerivedCategory.standard (ConstantCompletion.Mod (S.over V))
  have : PreservesFiniteLimits L := by
    dsimp only [L, localFixedPullback]
    infer_instance
  have : PreservesFiniteColimits L := by
    let Z := Functor.sheafPullbackConstruction.sheafPullback (Over.post G)
      (ModuleCat.{max v (u + 1)} B) (J.over W) (T.over (G.obj W))
    have : Z.IsLeftAdjoint :=
      (Functor.sheafPullbackConstruction.sheafAdjunctionContinuous (Over.post G)
        (ModuleCat.{max v (u + 1)} B) (J.over W) (T.over (G.obj W))).isLeftAdjoint
    change PreservesFiniteColimits (Z ⋙ T.overMapPullback _ f)
    exact comp_preservesFiniteColimits _ _
  have : L.Additive := Functor.additive_of_preserves_binary_products L
  let egeom := localFixedSquare J T G B W f
  let econst := localFixedConstant J T G B W f
  let Z := Functor.sheafPullbackConstruction.sheafPullback G
    (ModuleCat.{max v (u + 1)} B) J T
  have : Z.Additive := Functor.additive_of_preserves_binary_products Z
  have : Z.IsLeftAdjoint :=
    (Functor.sheafPullbackConstruction.sheafAdjunctionContinuous G
      (ModuleCat.{max v (u + 1)} B) J T).isLeftAdjoint
  let escalar : P ⋙ H ≅ F ⋙ Z := AlgebraicGeometry.ProEtale.comparison_scalars X B
  have : O.Additive := ringedOverFunctor_additive S V
  have : PreservesFiniteLimits O := ringedOverFunctor_preservesFiniteLimits S V
  have : PreservesFiniteColimits O := ringedOverFunctor_preservesFiniteColimits S V
  let eres : O ⋙ E ≅ H ⋙ Rp := sliceScalarsIso T B V
  let dE : ConstantCompletion.D (S.over V) ⥤
      CoefficientFixedDerivedCategory (T.over V) B := E.mapDerivedCategory
  have : dE.IsEquivalence := Functor.isEquivalence_mapDerivedCategory E
  let dL : CoefficientFixedDerivedCategory (J.over W) B ⥤
      CoefficientFixedDerivedCategory (T.over V) B := L.mapDerivedCategory
  let dO : ConstantCompletion.D S ⥤ ConstantCompletion.D (S.over V) := O.mapDerivedCategory
  let dC : DerivedCategory (ModuleCat.{max v (u + 1)} B) ⥤
      ConstantCompletion.D S := C.mapDerivedCategory
  let dconst : DerivedCategory (ModuleCat.{max v (u + 1)} B) ⥤
      CoefficientFixedDerivedCategory (T.over V) B :=
    (constantSheaf (T.over V) (ModuleCat.{max v (u + 1)} B)).mapDerivedCategory
  obtain ⟨em⟩ := hM
  let eleft : dE.obj (dO.obj (dC.obj (DerivedCategory.Q.obj M))) ≅
      dconst.obj (DerivedCategory.Q.obj M) :=
    (Functor.mapDerivedCategorySquareIso eres).app (dC.obj (DerivedCategory.Q.obj M)) ≪≫
      Rp.mapDerivedCategory.mapIso
        (((Functor.mapDerivedCategoryCompIso C H).app (DerivedCategory.Q.obj M)) ≪≫
          (Functor.mapDerivedCategoryNatIso (fixedConstantIso T B)).app
            (DerivedCategory.Q.obj M)) ≪≫
      ((Functor.mapDerivedCategoryCompIso
        (constantSheaf T (ModuleCat.{max v (u + 1)} B)) Rp).app
          (DerivedCategory.Q.obj M)) ≪≫
      (Functor.mapDerivedCategoryNatIso
        (T.overPullbackConstantSheafIso (ModuleCat.{max v (u + 1)} B) V)).app
          (DerivedCategory.Q.obj M)
  let eright : dE.obj (dO.obj ((adicFinitePullback.{u, v} X B).obj K)) ≅
      dconst.obj (DerivedCategory.Q.obj M) :=
    (Functor.mapDerivedCategorySquareIso eres).app
        ((adicFinitePullback.{u, v} X B).obj K) ≪≫
      Rp.mapDerivedCategory.mapIso
        (H.mapDerivedCategory.mapIso ((ep.app K).symm) ≪≫
          (Functor.mapDerivedCategorySquareIso escalar).app K) ≪≫
      (Functor.mapDerivedCategorySquareIso egeom).app (F.mapDerivedCategory.obj K) ≪≫
      dL.mapIso em ≪≫
      dL.mapIso (((constantSheaf (J.over W)
        (ModuleCat.{max v (u + 1)} B)).mapDerivedCategoryFactors).app M).symm ≪≫
      ((Functor.mapDerivedCategoryCompIso
        (constantSheaf (J.over W) (ModuleCat.{max v (u + 1)} B)) L).app
          (DerivedCategory.Q.obj M)) ≪≫
      (Functor.mapDerivedCategoryNatIso econst).app (DerivedCategory.Q.obj M)
  exact ⟨(Functor.FullyFaithful.ofFullyFaithful dE).preimageIso (eleft ≪≫ eright.symm)⟩

end AlgebraicGeometry.Scheme
