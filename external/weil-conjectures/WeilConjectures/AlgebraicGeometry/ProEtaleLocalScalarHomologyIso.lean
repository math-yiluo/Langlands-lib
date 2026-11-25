/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.AlgebraicGeometry.AdicStratifiedPerfectData
import WeilConjectures.Algebra.Homology.RingedSiteRestrictionKFlat
import all WeilConjectures.AlgebraicGeometry.DerivedScalarExtensionRestrictionAdjunction
import all WeilConjectures.AlgebraicGeometry.PbcActualScalarPullback
import WeilConjectures.AlgebraicGeometry.ProEtaleLocalDerivedRestrictionComparisons
import WeilConjectures.AlgebraicGeometry.ProEtaleModuleInverseImageComparison
import all WeilConjectures.AlgebraicGeometry.ProEtaleOperations
import all WeilConjectures.AlgebraicGeometry.RingedTopoiDerivedPullbackIndependent
import WeilConjectures.CategoryTheory.SiteModuleSliceSheafification

/-! # Local invariance of cohomology after derived scalar extension

Source: Stacks Project, Cohomology on Sites, derived pullback and
lemma-pullback-tensor-product; restriction-K-flat, Tag 0E8K.
-/

@[expose] public noncomputable section
set_option Elab.async false
set_option autoImplicit false
set_option synthInstance.maxSize 2048
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.Functor

namespace AlgebraicGeometry.Scheme

private theorem adjunctionSquare
    {A B C D : Type*} [Category A] [Category B] [Category C] [Category D]
    {E : A ⥤ B} {ER : B ⥤ A} {G : B ⥤ D} {GR : D ⥤ B}
    {F : A ⥤ C} {FR : C ⥤ A} {T : C ⥤ D} {TR : D ⥤ C}
    (a : E ⊣ ER) (b : G ⊣ GR) (c : F ⊣ FR) (d : T ⊣ TR)
    (δ : GR ⋙ ER ≅ TR ⋙ FR) : Nonempty (E ⋙ G ≅ F ⋙ T) :=
  ⟨((conjugateIsoEquiv (a.comp b) (c.comp d)).symm δ).symm⟩

section LocalScalarComparison

attribute [-instance] WeilConjectures.integralReductionSiteEssentiallySmall
  ProjectionRestriction.derivedOver ProjectionRestriction.derivedOverModules in
private theorem localWEquals (X : Scheme.{u}) :
    (ProEt.topology X).WEqualsLocallyBijective AddCommGrpCat.{u + 1} :=
  GrothendieckTopology.WEqualsLocallyBijective.ofEssentiallySmall.{u, u + 1,
    u + 1, u + 2, u + 1} (ProEt.topology X)

attribute [local instance 3000] localWEquals

attribute [local irreducible] completedAdicChangeData HasDerivedCategory.standard
  CochainComplex.IsKFlatIndependentCoefficients
  SheafOfModules.monoidalCategory proEtaleModuleInverseImage
  Functor.sheafPullbackConstruction.sheafPullback

attribute [-instance] WeilConjectures.integralReductionSiteEssentiallySmall
  ProjectionRestriction.derivedOver ProjectionRestriction.derivedOverModules in
private def scalarAdjunction (X : Scheme.{u})
    {R S : Sheaf (ProEt.topology X) CommRingCat.{u + 1}} (φ : R ⟶ S) :
    completedAdicChange X φ ⊣
      SheafOfModules.restrictScalars ((adicLisseForget X).map φ) :=
  pbcScalarAdjunction φ

attribute [-instance] WeilConjectures.integralReductionSiteEssentiallySmall
  ProjectionRestriction.derivedOver ProjectionRestriction.derivedOverModules in
private theorem scalarInverseIso {X Y : Scheme.{u}} (i : Y ⟶ X)
    {R S : Sheaf (ProEt.topology X) CommRingCat.{u + 1}} (φ : R ⟶ S) :
    Nonempty (completedAdicChange X φ ⋙ proEtaleModuleInverseImage i S ≅
      proEtaleModuleInverseImage i R ⋙ completedAdicChange Y
        ((proEtaleSheafInverseImage i CommRingCat.{u + 1}).map φ)) := by
  let RI := (proEtaleSheafInverseImage i CommRingCat.{u + 1}).obj R
  let SI := (proEtaleSheafInverseImage i CommRingCat.{u + 1}).obj S
  let ψ := (proEtaleSheafInverseImage i CommRingCat.{u + 1}).map φ
  let aR : (adicLisseForget X).obj R ⟶
      (proEtaleSheafDirectImage i RingCat.{u + 1}).obj ((adicLisseForget Y).obj RI) :=
    ⟨Functor.whiskerRight (proEtaleRingDirectImageMap i R RI (Iso.refl _)).hom
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})⟩
  let aS : (adicLisseForget X).obj S ⟶
      (proEtaleSheafDirectImage i RingCat.{u + 1}).obj ((adicLisseForget Y).obj SI) :=
    ⟨Functor.whiskerRight (proEtaleRingDirectImageMap i S SI (Iso.refl _)).hom
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})⟩
  have h : (adicLisseForget X).map φ ≫ aS = aR ≫
      (proEtaleSheafDirectImage i RingCat.{u + 1}).map ((adicLisseForget Y).map ψ) := by
    have hn := congrArg ((adicLisseForget X).map)
      ((proEtaleSheafAdjunction i CommRingCat.{u + 1}).unit.naturality φ)
    simp only [Functor.id_map, Functor.comp_map, Functor.map_comp] at hn
    simp only [aR, aS, proEtaleRingDirectImageMap, Iso.refl_hom]
    ext V x
    exact congrArg (fun k ↦ (k.hom.app V).hom x) hn
  let δ : proEtaleRingModuleDirectImage i S SI (Iso.refl _) ⋙
        SheafOfModules.restrictScalars ((adicLisseForget X).map φ) ≅
      SheafOfModules.restrictScalars ((adicLisseForget Y).map ψ) ⋙
        proEtaleRingModuleDirectImage i R RI (Iso.refl _) :=
    (scalar_right.{u} i ((adicLisseForget X).map φ)
      ((adicLisseForget Y).map ψ) aR aS h).exists.choose
  exact adjunctionSquare (E := completedAdicChange X φ)
    (G := proEtaleModuleInverseImage i S) (F := proEtaleModuleInverseImage i R)
    (T := completedAdicChange Y ψ)
    (ER := SheafOfModules.restrictScalars ((adicLisseForget X).map φ))
    (GR := proEtaleRingModuleDirectImage i S SI (Iso.refl _))
    (FR := proEtaleRingModuleDirectImage i R RI (Iso.refl _))
    (TR := SheafOfModules.restrictScalars ((adicLisseForget Y).map ψ))
    (scalarAdjunction X φ) (proEtaleModuleInverseImageAdjunction i S)
    (proEtaleModuleInverseImageAdjunction i R) (scalarAdjunction Y ψ) δ

attribute [-instance] WeilConjectures.integralReductionSiteEssentiallySmall
  ProjectionRestriction.derivedOver ProjectionRestriction.derivedOverModules in
private def completedTensorIso (X : Scheme.{u})
    {R S : Sheaf (ProEt.topology X) CommRingCat.{u + 1}} (φ : R ⟶ S) :
    completedAdicChange X φ ≅
      SheafOfModules.ScalarReductionProof.tensorFunctor.{u + 1, u, u + 1} φ :=
  (scalarAdjunction X φ).leftAdjointUniq
    (SheafOfModules.ScalarReductionProof.tensorAdjunction φ)

end LocalScalarComparison

attribute [-instance] WeilConjectures.integralReductionSiteEssentiallySmall
  ProjectionRestriction.derivedOver ProjectionRestriction.derivedOverModules in
private theorem complexCounit_isIso
    {A B : Type*} [Category A] [Category B] [Abelian A] [Abelian B]
    [HasDerivedCategory A] [HasDerivedCategory B]
    (F : A ⥤ B) [F.Additive] (LF : DerivedCategory A ⥤ DerivedCategory B)
    (ε : (DerivedCategory.Qh (C := A)) ⋙ LF ⟶
      F.mapHomotopyCategory (.up ℤ) ⋙ DerivedCategory.Qh (C := B))
    (P : CochainComplex A ℤ)
    [IsIso (ε.app ((HomotopyCategory.quotient A (.up ℤ)).obj P))] :
    IsIso ((complexCounit F LF ε).app P) := by
  simp only [complexCounit, NatTrans.comp_app, whiskerRight_app, whiskerLeft_app]
  infer_instance

attribute [-instance] WeilConjectures.integralReductionSiteEssentiallySmall
  ProjectionRestriction.derivedOver ProjectionRestriction.derivedOverModules in
private theorem derivedSquare
    {A B C D : Type*} [Category A] [Category B] [Category C] [Category D]
    [Abelian A] [Abelian B] [Abelian C] [Abelian D]
    [HasDerivedCategory A] [HasDerivedCategory B]
    [HasDerivedCategory C] [HasDerivedCategory D]
    (E : A ⥤ B) [E.Additive]
    (F : A ⥤ C) [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    (G : B ⥤ D) [G.Additive] [PreservesFiniteLimits G] [PreservesFiniteColimits G]
    (T : C ⥤ D) [T.Additive]
    (LE : DerivedCategory A ⥤ DerivedCategory B)
    (LT : DerivedCategory C ⥤ DerivedCategory D)
    (εE : DerivedCategory.Qh ⋙ LE ⟶ E.mapHomotopyCategory (.up ℤ) ⋙ DerivedCategory.Qh)
    (εT : DerivedCategory.Qh ⋙ LT ⟶ T.mapHomotopyCategory (.up ℤ) ⋙ DerivedCategory.Qh)
    (P : ObjectProperty (CochainComplex A ℤ))
    (hres : ∀ K : HomotopyCategory A (.up ℤ),
      ∃ (L : (show ObjectProperty (HomotopyCategory A (.up ℤ)) from
          fun K ↦ P K.as).FullSubcategory) (s : L.obj ⟶ K),
        HomotopyCategory.quasiIso A (.up ℤ) s)
    (he : ∀ K : P.FullSubcategory,
      IsIso (εE.app ((HomotopyCategory.quotient A (.up ℤ)).obj K.obj)))
    (ht : ∀ K : P.FullSubcategory,
      IsIso (εT.app ((HomotopyCategory.quotient C (.up ℤ)).obj
        ((F.mapHomologicalComplex (.up ℤ)).obj K.obj))))
    (b : E ⋙ G ≅ F ⋙ T) :
    Nonempty (LE ⋙ G.mapDerivedCategory ≅ F.mapDerivedCategory ⋙ LT) := by
  let : (F ⋙ T).Additive := by infer_instance
  let : (E ⋙ G).Additive := by infer_instance
  let ec := complexCounit E LE εE
  let tc := complexCounit T LT εT
  let l : DerivedCategory.Q ⋙ (LE ⋙ G.mapDerivedCategory) ⟶
      (E.mapHomologicalComplex (.up ℤ) ⋙ G.mapHomologicalComplex (.up ℤ)) ⋙
        DerivedCategory.Q :=
    whiskerRight ec G.mapDerivedCategory ≫
      whiskerLeft (E.mapHomologicalComplex (.up ℤ)) G.mapDerivedCategoryFactors.hom
  let r : DerivedCategory.Q ⋙ (F.mapDerivedCategory ⋙ LT) ⟶
      (F.mapHomologicalComplex (.up ℤ) ⋙ T.mapHomologicalComplex (.up ℤ)) ⋙
        DerivedCategory.Q :=
    whiskerRight F.mapDerivedCategoryFactors.hom LT ≫
      whiskerLeft (F.mapHomologicalComplex (.up ℤ)) tc
  let b₀ := Functor.mapHomologicalComplexCompIso (F := E) (G := G) (Iso.refl _) (.up ℤ) ≪≫
    NatIso.mapHomologicalComplex b (.up ℤ) ≪≫
    (Functor.mapHomologicalComplexCompIso (F := F) (G := T) (Iso.refl _) (.up ℤ)).symm
  have hl (K : P.FullSubcategory) : IsIso (l.app K.obj) := by
    let := he K
    let : IsIso (ec.app K.obj) := complexCounit_isIso E LE εE K.obj
    dsimp only [l, NatTrans.comp_app, whiskerRight_app, whiskerLeft_app]
    infer_instance
  have hr (K : P.FullSubcategory) : IsIso (r.app K.obj) := by
    let := ht K
    let : IsIso (tc.app ((F.mapHomologicalComplex (.up ℤ)).obj K.obj)) :=
      complexCounit_isIso T LT εT _
    dsimp only [r, NatTrans.comp_app, whiskerRight_app, whiskerLeft_app]
    infer_instance
  obtain ⟨e, _, _⟩ := comparison_on_resolutions P hres
    (LE ⋙ G.mapDerivedCategory) (F.mapDerivedCategory ⋙ LT) _ _ l r
      (Functor.isoWhiskerRight b₀ DerivedCategory.Q) hl hr
  exact ⟨e⟩

attribute [-instance] WeilConjectures.integralReductionSiteEssentiallySmall
  ProjectionRestriction.derivedOver ProjectionRestriction.derivedOverModules in
attribute [local irreducible] SheafOfModules.monoidalCategory in
private theorem tensorOverIso
    {C : Type (u + 1)} [Category.{u} C] [EssentiallySmall.{u + 1} C]
    {J : GrothendieckTopology C} {R S : Sheaf J CommRingCat.{u + 1}}
    (φ : R ⟶ S) (U : C) :
    Nonempty (SheafOfModules.ScalarReductionProof.tensorFunctor.{u + 1, u, u + 1} φ ⋙
        SheafOfModules.overFunctor
          ((sheafCompose J (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj S) U ≅
      SheafOfModules.overFunctor
        ((sheafCompose J (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj R) U ⋙
        SheafOfModules.ScalarReductionProof.tensorFunctor.{u + 1, u, u + 1}
          ((J.overPullback CommRingCat.{u + 1} U).map φ)) := by
  let A := (sheafCompose J (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj R
  let B := (sheafCompose J (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj S
  let ψ := (J.overPullback CommRingCat.{u + 1} U).map φ
  let E := SheafOfModules.ScalarReductionProof.tensorPresheafFunctor.{u + 1, u, u + 1} φ
  let E' := SheafOfModules.ScalarReductionProof.tensorPresheafFunctor.{u + 1, u, u + 1} ψ
  let T := SheafOfModules.slicePresheafRestrictionIndependent (J := J.over U) (Over.forget U) B
  let F := SheafOfModules.overFunctor A U
  let raw : E ⋙ T ≅ F ⋙ E' := by
    refine NatIso.ofComponents (fun M ↦ PresheafOfModules.isoMk (fun V ↦ Iso.refl _) ?_) ?_
    · intro V W g
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      intro z
      induction z using TensorProduct.inductionOn with
      | add z t hz ht => simp only [_root_.map_add, hz, ht]
      | tmul b m =>
        exact ((SheafOfModules.exists_changeOfRingsMap φ M
          ((Over.forget U).op.map g)).choose_spec b m).trans
            ((SheafOfModules.exists_changeOfRingsMap ψ (M.over U) g).choose_spec b m).symm
    · intro M N f
      apply PresheafOfModules.hom_ext
      intro V
      simp only [Functor.comp_map]
      rfl
  have := SheafOfModules.sliceSheafificationComparisonIndependent_isIso
    (J := J.over U) (Over.forget U) B
  exact ⟨Functor.isoWhiskerLeft E
      (asIso (SheafOfModules.sliceSheafificationComparisonIndependent
        (J := J.over U) (Over.forget U) B)).symm ≪≫
    Functor.isoWhiskerRight raw (PresheafOfModules.sheafification (𝟙 (B.over U).obj))⟩

private def overUnderlyingIso
    {C : Type*} [Category C] (J : GrothendieckTopology C)
    (R : Sheaf J RingCat.{u + 1}) (U : C) :
    SheafOfModules.overFunctor.{u + 1} R U ⋙ SheafOfModules.toSheaf (R.over U) ≅
      SheafOfModules.toSheaf R ⋙ J.overPullback AddCommGrpCat.{u + 1} U :=
  NatIso.ofComponents (fun _ ↦ Iso.refl _) (by intros; rfl)

set_option backward.isDefEq.respectTransparency true

section LocalScalarComparison

attribute [local instance 3000] localWEquals
attribute [local irreducible] completedAdicChangeData HasDerivedCategory.standard
  CochainComplex.IsKFlatIndependentCoefficients
  SheafOfModules.monoidalCategory proEtaleModuleInverseImage
  Functor.sheafPullbackConstruction.sheafPullback

attribute [-instance] WeilConjectures.integralReductionSiteEssentiallySmall
  ProjectionRestriction.derivedOver ProjectionRestriction.derivedOverModules in
@[instance_reducible]
private def sliceDerived (X : Scheme.{u}) (U : X.ProEt)
    (R : Sheaf ((ProEt.topology X).over U) RingCat.{u + 1}) :
    HasDerivedCategory (SheafOfModules.{u + 1} R) :=
  HasDerivedCategory.standard _

attribute [local instance 3000] sliceDerived

attribute [-instance] WeilConjectures.integralReductionSiteEssentiallySmall
  ProjectionRestriction.derivedOver ProjectionRestriction.derivedOverModules in
private def localFunctor {X Y : Scheme.{u}} (i : Y ⟶ X)
    (R : Sheaf (ProEt.topology X) CommRingCat.{u + 1}) (U : Y.ProEt) :
    proEtaleRingModules X R ⥤
      SheafOfModules.{u + 1} ((ProEtaleLocalRestriction.inverseRing i R).over U) :=
  proEtaleModuleInverseImage i R ⋙ ProEtaleLocalRestriction.restriction i R U

attribute [-instance] WeilConjectures.integralReductionSiteEssentiallySmall
  ProjectionRestriction.derivedOver ProjectionRestriction.derivedOverModules in
private theorem localFunctor_additive {X Y : Scheme.{u}} (i : Y ⟶ X)
    (R : Sheaf (ProEt.topology X) CommRingCat.{u + 1}) (U : Y.ProEt) :
    (localFunctor i R U).Additive := by
  unfold localFunctor
  infer_instance

attribute [-instance] WeilConjectures.integralReductionSiteEssentiallySmall
  ProjectionRestriction.derivedOver ProjectionRestriction.derivedOverModules in
private theorem localFunctor_limits {X Y : Scheme.{u}} (i : Y ⟶ X)
    (R : Sheaf (ProEt.topology X) CommRingCat.{u + 1}) (U : Y.ProEt) :
    PreservesFiniteLimits (localFunctor i R U) := by
  unfold localFunctor
  exact comp_preservesFiniteLimits _ _

attribute [-instance] WeilConjectures.integralReductionSiteEssentiallySmall
  ProjectionRestriction.derivedOver ProjectionRestriction.derivedOverModules in
private theorem localFunctor_colimits {X Y : Scheme.{u}} (i : Y ⟶ X)
    (R : Sheaf (ProEt.topology X) CommRingCat.{u + 1}) (U : Y.ProEt) :
    PreservesFiniteColimits (localFunctor i R U) := by
  unfold localFunctor
  exact comp_preservesFiniteColimits _ _

attribute [local instance] localFunctor_additive localFunctor_limits localFunctor_colimits

attribute [-instance] WeilConjectures.integralReductionSiteEssentiallySmall
  ProjectionRestriction.derivedOver ProjectionRestriction.derivedOverModules in
private def identityPullIso {X Y : Scheme.{u}} (i : Y ⟶ X)
    (R : Sheaf (ProEt.topology X) CommRingCat.{u + 1}) :
    proEtaleRingModulePullback i R
        ((proEtaleSheafInverseImage i CommRingCat.{u + 1}).obj R) (Iso.refl _) ≅
      proEtaleModuleInverseImage i R := by
  let B := (proEtaleSheafInverseImage i CommRingCat.{u + 1}).obj R
  let H := proEtaleModuleInverseImage i R
  let r : SheafOfModules.restrictScalars ((adicLisseForget Y).map (𝟙 B)) ≅
      𝟭 (proEtaleRingModules Y B) :=
    NatIso.ofComponents (fun M ↦
      (SheafOfModules.fullyFaithfulForget _).preimageIso
        (PresheafOfModules.isoMk
          (fun U ↦ ModuleCat.restrictScalarsId'App _ rfl (M.val.obj U))
          (by intros; ext x; rfl))) (by intros; ext U x; rfl)
  let a := proEtaleRingExtensionAdjunction i R B (Iso.refl _)
  let b := (Adjunction.id (C := proEtaleRingModules Y B)).ofNatIsoRight r.symm
  exact Functor.isoWhiskerLeft H (a.leftAdjointUniq b) ≪≫ Functor.rightUnitor H

attribute [-instance] WeilConjectures.integralReductionSiteEssentiallySmall
  ProjectionRestriction.derivedOver ProjectionRestriction.derivedOverModules in
private def localRestrictionIso {X Y : Scheme.{u}} (i : Y ⟶ X)
    (R : Sheaf (ProEt.topology X) CommRingCat.{u + 1}) (U : Y.ProEt)
    (K : DerivedCategory (proEtaleRingModules X R)) :
    sfbLocalRestriction i R U K ≅ (localFunctor i R U).mapDerivedCategory.obj K := by
  let B := (proEtaleSheafInverseImage i CommRingCat.{u + 1}).obj R
  let G := proEtaleRingModulePullback i R B (Iso.refl _)
  let T := ProEtaleLocalRestriction.restriction i R U
  let C := DerivedCategory.Q.objPreimage K
  let L := G.mapDerivedCategory.obj K
  let D := DerivedCategory.Q.objPreimage L
  change DerivedCategory.Q.obj ((T.mapHomologicalComplex (.up ℤ)).obj D) ≅ _
  refine (T.mapDerivedCategoryFactors.app D).symm ≪≫
    T.mapDerivedCategory.mapIso (DerivedCategory.Q.objObjPreimageIso L) ≪≫
    T.mapDerivedCategory.mapIso
      (G.mapDerivedCategory.mapIso (DerivedCategory.Q.objObjPreimageIso K).symm) ≪≫
    T.mapDerivedCategory.mapIso (G.mapDerivedCategoryFactors.app C) ≪≫
    T.mapDerivedCategory.mapIso (DerivedCategory.Q.mapIso
      ((NatIso.mapHomologicalComplex (identityPullIso i R) (.up ℤ)).app C)) ≪≫
    (T.mapDerivedCategoryFactors.app _) ≪≫ ?_
  exact ((localFunctor i R U).mapDerivedCategoryFactors.app C).symm ≪≫
    (localFunctor i R U).mapDerivedCategory.mapIso
      (DerivedCategory.Q.objObjPreimageIso K)

set_option linter.defProp false in
attribute [-instance] WeilConjectures.integralReductionSiteEssentiallySmall
  ProjectionRestriction.derivedOver ProjectionRestriction.derivedOverModules in
private def sliceChangeData {X Y : Scheme.{u}} (i : Y ⟶ X)
    {R S : Sheaf (ProEt.topology X) CommRingCat.{u + 1}} (φ : R ⟶ S) (U : Y.ProEt) :=
  SheafOfModules.derivedChangeOfRingsIndependentCoefficients.{u + 2, u + 1, u + 1, u}
    (((ProEt.topology Y).overPullback CommRingCat.{u + 1} U).map
      ((proEtaleSheafInverseImage i CommRingCat.{u + 1}).map φ))

attribute [local irreducible] sliceChangeData

attribute [-instance] WeilConjectures.integralReductionSiteEssentiallySmall
  ProjectionRestriction.derivedOver ProjectionRestriction.derivedOverModules in
private abbrev localModules {X Y : Scheme.{u}} (i : Y ⟶ X)
    (R : Sheaf (ProEt.topology X) CommRingCat.{u + 1}) (U : Y.ProEt) :=
  SheafOfModules.{u + 1}
    (((adicLisseForget Y).obj
      ((proEtaleSheafInverseImage i CommRingCat.{u + 1}).obj R)).over U)

attribute [-instance] WeilConjectures.integralReductionSiteEssentiallySmall
  ProjectionRestriction.derivedOver ProjectionRestriction.derivedOverModules in
private def sliceChange {X Y : Scheme.{u}} (i : Y ⟶ X)
    {R S : Sheaf (ProEt.topology X) CommRingCat.{u + 1}} (φ : R ⟶ S) (U : Y.ProEt) :
    localModules i R U ⥤ localModules i S U :=
  (sliceChangeData i φ U).choose

attribute [-instance] WeilConjectures.integralReductionSiteEssentiallySmall
  ProjectionRestriction.derivedOver ProjectionRestriction.derivedOverModules in
private def sliceTensorIso {X Y : Scheme.{u}} (i : Y ⟶ X)
    {R S : Sheaf (ProEt.topology X) CommRingCat.{u + 1}} (φ : R ⟶ S) (U : Y.ProEt) :
    sliceChange i φ U ≅ SheafOfModules.ScalarReductionProof.tensorFunctor.{u + 1, u, u + 1}
      (K := (ProEt.topology Y).over U)
      (((ProEt.topology Y).overPullback CommRingCat.{u + 1} U).map
        ((proEtaleSheafInverseImage i CommRingCat.{u + 1}).map φ)) :=
  ((SheafOfModules.ScalarReductionProof.tensorAdjunction_of_identifications.{u + 1, u, u + 1}
    (K := (ProEt.topology Y).over U)
    (((ProEt.topology Y).overPullback CommRingCat.{u + 1} U).map
      ((proEtaleSheafInverseImage i CommRingCat.{u + 1}).map φ))
    (sliceChange i φ U) (sliceChangeData i φ U).choose_spec.choose
    (sliceChangeData i φ U).choose_spec.choose_spec.choose).choose).leftAdjointUniq
      (SheafOfModules.ScalarReductionProof.tensorAdjunction.{u + 1, u, u + 1}
        (K := (ProEt.topology Y).over U)
        (((ProEt.topology Y).overPullback CommRingCat.{u + 1} U).map
          ((proEtaleSheafInverseImage i CommRingCat.{u + 1}).map φ)))

attribute [-instance] WeilConjectures.integralReductionSiteEssentiallySmall
  ProjectionRestriction.derivedOver ProjectionRestriction.derivedOverModules in
private def ordinaryLocalScalarIso {X Y : Scheme.{u}} (i : Y ⟶ X)
    {R S : Sheaf (ProEt.topology X) CommRingCat.{u + 1}} (φ : R ⟶ S) (U : Y.ProEt) :
    completedAdicChange X φ ⋙ localFunctor i S U ≅
      localFunctor i R U ⋙ sliceChange i φ U := by
  unfold localFunctor
  exact (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight (scalarInverseIso i φ).some _ ≪≫
    Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft (proEtaleModuleInverseImage i R)
      (Functor.isoWhiskerRight
          (completedTensorIso Y ((proEtaleSheafInverseImage i CommRingCat.{u + 1}).map φ)) _ ≪≫
        (tensorOverIso _ U).some ≪≫ Functor.isoWhiskerLeft _ (sliceTensorIso i φ U).symm) ≪≫
    (Functor.associator _ _ _).symm

attribute [-instance] WeilConjectures.integralReductionSiteEssentiallySmall
  ProjectionRestriction.derivedOver ProjectionRestriction.derivedOverModules in
private theorem localFunctor_kflat {X Y : Scheme.{u}} (i : Y ⟶ X)
    (R : Sheaf (ProEt.topology X) CommRingCat.{u + 1}) (U : Y.ProEt)
    (P : CochainComplex (proEtaleRingModules X R) ℤ)
    (hp : CochainComplex.IsKFlatIndependentCoefficients (R := R) P)
    (hf : ∀ n : ℤ, SheafOfModules.IsFlatOnSite.{u + 1, u, u + 1, u + 1}
      (J := ProEt.topology X) (R := R) (P.X n)) :
    CochainComplex.IsKFlatIndependentCoefficients
      (R := ((proEtaleSheafInverseImage i CommRingCat.{u + 1}).obj R).over U)
      (((localFunctor i R U).mapHomologicalComplex (.up ℤ)).obj P) := by
  let RI := (proEtaleSheafInverseImage i CommRingCat.{u + 1}).obj R
  obtain ⟨I, hI⟩ := proEtaleAlgebraicInverseImage_exists i R
  have : PreservesFiniteLimits (proEtaleSheafInverseImage i (Type (u + 1))) :=
    (AlgebraicGeometry.ProEtale.toposFunctorialityInverseImage i (𝟙 X)).2.2.2.1
  let : I.modules.Additive := by
    rw [hI]
    infer_instance
  have hh := SheafOfModules.kFlat_inverseImage_independent.{u + 1, u, u + 1, u, u + 1}
    (proEtaleSheafInverseImage i (Type (u + 1)))
    (proEtaleSheafDirectImage i (Type (u + 1)))
    (proEtaleSheafAdjunction i (Type (u + 1))) I P hp hf
  have hh' := SheafOfModules.kFlat_of_iso_independent (R := RI)
    ((NatIso.mapHomologicalComplex (eqToIso hI) (.up ℤ)).app P) hh
  exact (SheafOfModules.ringedSite_restriction_exact_kflat.{u + 1, u, 0}
    (ProEt.topology Y) RI U).2.2 _ hh'

attribute [-instance] WeilConjectures.integralReductionSiteEssentiallySmall
  ProjectionRestriction.derivedOver ProjectionRestriction.derivedOverModules in
private theorem sliceChange_additive {X Y : Scheme.{u}} (i : Y ⟶ X)
    {R S : Sheaf (ProEt.topology X) CommRingCat.{u + 1}} (φ : R ⟶ S) (U : Y.ProEt) :
    (sliceChange i φ U).Additive :=
  (sliceChangeData i φ U).choose_spec.choose_spec.choose_spec.choose

attribute [local instance] sliceChange_additive

attribute [local irreducible] sliceChange Functor.mapHomotopyCategory DerivedCategory.Qh

attribute [-instance] WeilConjectures.integralReductionSiteEssentiallySmall
  ProjectionRestriction.derivedOver ProjectionRestriction.derivedOverModules in
private theorem sliceDerivedExistence {X Y : Scheme.{u}} (i : Y ⟶ X)
    {R S : Sheaf (ProEt.topology X) CommRingCat.{u + 1}} (φ : R ⟶ S) (U : Y.ProEt) :
    ∃ (LF : DerivedCategory (localModules i R U) ⥤ DerivedCategory (localModules i S U))
      (ε : DerivedCategory.Qh (C := localModules i R U) ⋙ LF ⟶
        (sliceChange i φ U).mapHomotopyCategory (.up ℤ) ⋙
          DerivedCategory.Qh (C := localModules i S U)),
      LF.IsLeftDerivedFunctor ε (HomotopyCategory.quasiIso (localModules i R U) (.up ℤ)) ∧
        (∃ (_ : LF.CommShift ℤ), LF.IsTriangulated) ∧
        ∀ P : CochainComplex (localModules i R U) ℤ,
          CochainComplex.IsKFlatIndependentCoefficients
            (R := ((proEtaleSheafInverseImage i CommRingCat.{u + 1}).obj R).over U) P →
          IsIso (ε.app ((HomotopyCategory.quotient (localModules i R U) (.up ℤ)).obj P)) := by
  unfold sliceChange
  obtain ⟨LF, ε, hu, ht, hk⟩ :=
    (sliceChangeData i φ U).choose_spec.choose_spec.choose_spec.choose_spec.2.2
  exact ⟨LF, ε, hu, ht, hk⟩

attribute [-instance] WeilConjectures.integralReductionSiteEssentiallySmall
  ProjectionRestriction.derivedOver ProjectionRestriction.derivedOverModules in
private def sliceDerivedChange {X Y : Scheme.{u}} (i : Y ⟶ X)
    {R S : Sheaf (ProEt.topology X) CommRingCat.{u + 1}} (φ : R ⟶ S) (U : Y.ProEt) :
    DerivedCategory (localModules i R U) ⥤ DerivedCategory (localModules i S U) :=
  (sliceDerivedExistence i φ U).choose

attribute [-instance] WeilConjectures.integralReductionSiteEssentiallySmall
  ProjectionRestriction.derivedOver ProjectionRestriction.derivedOverModules in
private def sliceCounit {X Y : Scheme.{u}} (i : Y ⟶ X)
    {R S : Sheaf (ProEt.topology X) CommRingCat.{u + 1}} (φ : R ⟶ S) (U : Y.ProEt) :
    DerivedCategory.Qh (C := localModules i R U) ⋙ sliceDerivedChange i φ U ⟶
      (sliceChange i φ U).mapHomotopyCategory (.up ℤ) ⋙
        DerivedCategory.Qh (C := localModules i S U) :=
  (sliceDerivedExistence i φ U).choose_spec.choose

attribute [-instance] WeilConjectures.integralReductionSiteEssentiallySmall
  ProjectionRestriction.derivedOver ProjectionRestriction.derivedOverModules in
private theorem sliceCounit_isIso {X Y : Scheme.{u}} (i : Y ⟶ X)
    {R S : Sheaf (ProEt.topology X) CommRingCat.{u + 1}} (φ : R ⟶ S) (U : Y.ProEt)
    (P : CochainComplex (localModules i R U) ℤ)
    (hP : CochainComplex.IsKFlatIndependentCoefficients
      (R := ((proEtaleSheafInverseImage i CommRingCat.{u + 1}).obj R).over U) P) :
    IsIso ((sliceCounit i φ U).app
      ((HomotopyCategory.quotient (localModules i R U) (.up ℤ)).obj P)) := by
  unfold sliceCounit
  exact (sliceDerivedExistence i φ U).choose_spec.choose_spec.2.2 P hP

attribute [-instance] WeilConjectures.integralReductionSiteEssentiallySmall
  ProjectionRestriction.derivedOver ProjectionRestriction.derivedOverModules in
private def globalCounit (X : Scheme.{u})
    {R S : Sheaf (ProEt.topology X) CommRingCat.{u + 1}} (φ : R ⟶ S) :=
  pbcExtensionCounit φ

attribute [local irreducible] sliceDerivedChange completedAdicChange
  completedAdicDerivedChange localFunctor

attribute [local irreducible] Functor.mapDerivedCategory DerivedCategory.Q

attribute [-instance] WeilConjectures.integralReductionSiteEssentiallySmall
  ProjectionRestriction.derivedOver ProjectionRestriction.derivedOverModules in
private theorem derivedLocalScalarIso {X Y : Scheme.{u}} (i : Y ⟶ X)
    {R S : Sheaf (ProEt.topology X) CommRingCat.{u + 1}} (φ : R ⟶ S) (U : Y.ProEt) :
    Nonempty (completedAdicDerivedChange X φ ⋙ (localFunctor i S U).mapDerivedCategory ≅
      (localFunctor i R U).mapDerivedCategory ⋙ sliceDerivedChange i φ U) := by
  let C := proEtaleRingModules X R
  let P : ObjectProperty (CochainComplex C ℤ) := fun K ↦
    CochainComplex.IsKFlatIndependentCoefficients (R := R) K ∧
      ∀ n : ℤ, SheafOfModules.IsFlatOnSite.{u + 1, u, u + 1, u + 1}
        (J := ProEt.topology X) (R := R) (K.X n)
  let H : ObjectProperty (HomotopyCategory C (.up ℤ)) := fun K ↦ P K.as
  have hres : ∀ K : HomotopyCategory C (.up ℤ),
      ∃ (L : H.FullSubcategory) (s : L.obj ⟶ K),
        HomotopyCategory.quasiIso C (.up ℤ) s := by
    intro K
    obtain ⟨L, s, hl, hf, hs, _⟩ :=
      CochainComplex.exists_isKFlatResolutionIndependentCoefficients (J := ProEt.topology X)
        (R := R) K.as
    refine ⟨⟨(HomotopyCategory.quotient C (.up ℤ)).obj L, hl, ?_⟩,
      (HomotopyCategory.quotient C (.up ℤ)).map s,
      (HomotopyCategory.quotient_map_mem_quasiIso_iff s).2 hs⟩
    intro n
    exact (exactFunctor _ _).prop_of_iso
      (SheafOfModules.siteSheafTensorRightIso R (L.X n)).symm (hf n)
  let E : C ⥤ proEtaleRingModules X S := completedAdicChange X φ
  let F : C ⥤ localModules i R U := localFunctor i R U
  let G : proEtaleRingModules X S ⥤ localModules i S U := localFunctor i S U
  let T : localModules i R U ⥤ localModules i S U := sliceChange i φ U
  let : E.Additive := completedAdicChange_additive X φ
  let : F.Additive := localFunctor_additive i R U
  let : G.Additive := localFunctor_additive i S U
  let : T.Additive := sliceChange_additive i φ U
  let LE : DerivedCategory C ⥤ DerivedCategory (proEtaleRingModules X S) :=
    completedAdicDerivedChange X φ
  let LT : DerivedCategory (localModules i R U) ⥤ DerivedCategory (localModules i S U) :=
    sliceDerivedChange i φ U
  have he (K : P.FullSubcategory) :
      IsIso ((globalCounit X φ).app ((HomotopyCategory.quotient C (.up ℤ)).obj K.obj)) := by
    unfold globalCounit
    exact pbcExtensionCounit_isIso φ K.obj K.property.1
  have ht (K : P.FullSubcategory) :
      IsIso ((sliceCounit i φ U).app ((HomotopyCategory.quotient (localModules i R U)
        (.up ℤ)).obj ((F.mapHomologicalComplex (.up ℤ)).obj K.obj))) := by
    exact sliceCounit_isIso i φ U ((F.mapHomologicalComplex (.up ℤ)).obj K.obj)
      (localFunctor_kflat i R U K.obj K.property.1 K.property.2)
  have b : E ⋙ G ≅ F ⋙ T := ordinaryLocalScalarIso i φ U
  have h := derivedSquare (A := C) (B := proEtaleRingModules X S)
    (C := localModules i R U) (D := localModules i S U)
    E F G T LE LT (globalCounit X φ) (sliceCounit i φ U) P hres he ht b
  exact h

attribute [-instance] WeilConjectures.integralReductionSiteEssentiallySmall
  ProjectionRestriction.derivedOver ProjectionRestriction.derivedOverModules in
private def underlyingLocalIso {X Y : Scheme.{u}} (i : Y ⟶ X)
    (R : Sheaf (ProEt.topology X) CommRingCat.{u + 1}) (U : Y.ProEt) :
    localFunctor i R U ⋙ SheafOfModules.toSheaf _ ≅
      SheafOfModules.toSheaf ((adicLisseForget X).obj R) ⋙
        proEtaleSheafInverseImage i AddCommGrpCat.{u + 1} ⋙
          (ProEt.topology Y).overPullback AddCommGrpCat.{u + 1} U := by
  let e := (proEtale_moduleInverseImage_comparison i R).1.some
  unfold localFunctor
  exact Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft (proEtaleModuleInverseImage i R)
      (overUnderlyingIso (ProEt.topology Y) (ProEtaleLocalRestriction.inverseRing i R) U) ≪≫
    (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight e ((ProEt.topology Y).overPullback AddCommGrpCat.{u + 1} U) ≪≫
    Functor.associator _ _ _

end LocalScalarComparison

attribute [-instance] WeilConjectures.integralReductionSiteEssentiallySmall
  ProjectionRestriction.derivedOver ProjectionRestriction.derivedOverModules in
attribute [local irreducible] completedAdicChangeData HasDerivedCategory.standard
  CochainComplex.IsKFlatIndependentCoefficients sliceChangeData
  sliceChange sliceDerivedChange completedAdicChange completedAdicDerivedChange localFunctor
  SheafOfModules.monoidalCategory proEtaleModuleInverseImage
  Functor.sheafPullbackConstruction.sheafPullback in
/-- Derived scalar-extension cohomology on a slice depends only on the local derived
object over the original coefficients. The coefficient map is arbitrary, and neither
object is assumed bounded, perfect, or complete.

Source: Stacks Project, Cohomology on Sites, lemma-pullback-K-flat,
lemma-pullback-tensor-product and lemma-restriction-K-flat (Tag 0E8K);
Bhatt--Scholze, Proposition 6.6.11, local residue calculation.
(auxiliary; not a blueprint node).

Proof: write R'=i^{-1}R and S'=i^{-1}S. Module inverse image over the actual
inverse-image ring and restriction to U are exact. Resolve an arbitrary R-complex
by a K-flat complex with flat terms. Its inverse image is K-flat with flat terms,
and slice restriction retains K-flatness. The ordinary scalar-extension comparison
identifies i^{-1}(S tensor_R C)|_U with S'|_U tensor_(R'|_U) (i^{-1}C)|_U:
it sends the inverse image of a local pure tensor to the tensor of its inverse
images. Balancing gives the inverse map; both commute with the differentials.
The K-flat computation counits identify this comparison with the two derived
composites, independently of the resolution. Their naturality descends through
localization. The identity-coefficient pullback in sfbLocalRestriction is the exact
module inverse image: extension along the identity is its tensor unitor.
Its localization-representative isomorphism and the exact slice factor identify
sfbLocalRestriction with this composite. Apply local derived scalar extension to e
and conjugate by these comparisons at K and K'. Finally commute homology with exact
inverse image, slice restriction, and the underlying additive-sheaf functor. The
result is the displayed isomorphism. The construction also applies to zero rings,
empty slices and unbounded objects, and uses no infinite-limit preservation. -/
theorem proEtaleLocalScalarHomologyIso {X Y : Scheme.{u}} (i : Y ⟶ X)
    {R S : Sheaf (ProEt.topology X) CommRingCat.{u + 1}} (φ : R ⟶ S)
    (U : Y.ProEt) (K K' : DerivedCategory (proEtaleRingModules X R))
    (e : sfbLocalRestriction i R U K ≅ sfbLocalRestriction i R U K') (q : ℤ) :
    Nonempty
      (((ProEt.topology Y).overPullback AddCommGrpCat.{u + 1} U).obj
          ((proEtaleSheafInverseImage i AddCommGrpCat.{u + 1}).obj
            ((SheafOfModules.toSheaf ((adicLisseForget X).obj S)).obj
              ((DerivedCategory.homologyFunctor _ q).obj
                ((completedAdicDerivedChange X φ).obj K)))) ≅
        ((ProEt.topology Y).overPullback AddCommGrpCat.{u + 1} U).obj
          ((proEtaleSheafInverseImage i AddCommGrpCat.{u + 1}).obj
            ((SheafOfModules.toSheaf ((adicLisseForget X).obj S)).obj
              ((DerivedCategory.homologyFunctor _ q).obj
                ((completedAdicDerivedChange X φ).obj K'))))) := by
  let := localWEquals X
  let := localWEquals Y
  let : HasDerivedCategory (localModules i R U) :=
    sliceDerived Y U ((ProEtaleLocalRestriction.inverseRing i R).over U)
  let : HasDerivedCategory (localModules i S U) :=
    sliceDerived Y U ((ProEtaleLocalRestriction.inverseRing i S).over U)
  let : (localFunctor i R U).Additive := localFunctor_additive i R U
  let : PreservesFiniteLimits (localFunctor i R U) := localFunctor_limits i R U
  let : PreservesFiniteColimits (localFunctor i R U) := localFunctor_colimits i R U
  let : (localFunctor i S U).Additive := localFunctor_additive i S U
  let : PreservesFiniteLimits (localFunctor i S U) := localFunctor_limits i S U
  let : PreservesFiniteColimits (localFunctor i S U) := localFunctor_colimits i S U
  obtain ⟨c⟩ := derivedLocalScalarIso i φ U
  let E := sliceDerivedChange i φ U
  let h : (localFunctor i S U).mapDerivedCategory.obj
        ((completedAdicDerivedChange X φ).obj K) ≅
      (localFunctor i S U).mapDerivedCategory.obj
        ((completedAdicDerivedChange X φ).obj K') :=
    c.app K ≪≫ E.mapIso
      ((localRestrictionIso i R U K).symm ≪≫ e ≪≫ localRestrictionIso i R U K') ≪≫
        (c.app K').symm
  let F := localFunctor i S U
  let V := SheafOfModules.toSheaf.{u + 1}
    (((adicLisseForget Y).obj
      ((proEtaleSheafInverseImage i CommRingCat.{u + 1}).obj S)).over U)
  let H := DerivedCategory.homologyFunctor (proEtaleRingModules X S) q
  let d := F.mapDerivedCategoryHomologyFunctorIso q
  exact ⟨((underlyingLocalIso i S U).app (H.obj ((completedAdicDerivedChange X φ).obj K))).symm
    ≪≫ V.mapIso ((d.app _ ≪≫ (DerivedCategory.homologyFunctor _ q).mapIso h) ≪≫ (d.app _).symm)
    ≪≫ (underlyingLocalIso i S U).app (H.obj ((completedAdicDerivedChange X φ).obj K'))⟩

end AlgebraicGeometry.Scheme
