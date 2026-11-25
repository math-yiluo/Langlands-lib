/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.CategoryTheory.Projection.ProjectionFormulaBaseChangeNaturality
public import Mathlib.CategoryTheory.Triangulated.Functor
public import WeilConjectures.CategoryTheory.Ringed.RingedDerivedRestrictionGeneralSupplement
import WeilConjectures.AlgebraicGeometry.Ringed.RingedProjectionRestriction
import WeilConjectures.AlgebraicGeometry.ProEtale.Projection.ProEtaleProjectionGlobalComparison
import WeilConjectures.AlgebraicGeometry.ProjectionRestriction.RingedProjectionTensorExact
import Mathlib.CategoryTheory.Triangulated.Adjunction

/-!
# The actual projection mate on a pro-etale slice

## References

* Stacks, Modules on Sites, Tag 04IF
* Cohomology on Sites, Tags 08FI and 0B56
* Stacks Project, Tags 04IF, 08FI, 07A4 and 0B56
-/

@[expose] public noncomputable section
set_option autoImplicit false

attribute [local instance 100] HasDerivedCategory.standard
universe u
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.Scheme
variable {X Y : Scheme.{u}} (f : X ⟶ Y)
  (R : Sheaf (ProEt.topology Y) CommRingCat.{u + 1})
  (S : Sheaf (ProEt.topology X) CommRingCat.{u + 1})
  (c : (proEtaleSheafInverseImage f CommRingCat.{u + 1}).obj R ≅ S)
  (a : ProEtaleTensorModel Y R) (b : ProEtaleTensorModel X S)
  (E : DerivedCategory (proEtaleRingModules X S))

/-- A slice presentation of the actual mate, without a perfectness hypothesis.
The two functors and their comparisons are ordinary derived functors on the slice. -/
structure ProEtaleProjectionMateSlicePresentation (U : Y.ProEt) where
  source : DerivedCategory (SheafOfModules.{u + 1}
      (((sheafCompose (ProEt.topology Y)
        (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj R).over U)) ⥤
    DerivedCategory (SheafOfModules.{u + 1}
      (((sheafCompose (ProEt.topology Y)
        (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj R).over U))
  target : DerivedCategory (SheafOfModules.{u + 1}
      (((sheafCompose (ProEt.topology Y)
        (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj R).over U)) ⥤
    DerivedCategory (SheafOfModules.{u + 1}
      (((sheafCompose (ProEt.topology Y)
        (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj R).over U))
  [sourceShift : source.CommShift ℤ]
  [targetShift : target.CommShift ℤ]
  sourceExact : source.IsTriangulated
  targetExact : target.IsTriangulated
  mate : source ⟶ target
  shiftCompatible : NatTrans.CommShift mate ℤ
  sourceComparison : (Functor.curryObj a.tensor).obj
      ((proEtaleRingDerivedDirectImage f R S c).obj E) ⋙
      ringedDerivedRestrictionGeneral ((sheafCompose (ProEt.topology Y)
        (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj R) U ≅
    ringedDerivedRestrictionGeneral ((sheafCompose (ProEt.topology Y)
        (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj R) U ⋙ source
  targetComparison : (proEtaleRingDerivedPullback f R S c ⋙
      (Functor.curryObj b.tensor).obj E ⋙ proEtaleRingDerivedDirectImage f R S c) ⋙
      ringedDerivedRestrictionGeneral ((sheafCompose (ProEt.topology Y)
        (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj R) U ≅
    ringedDerivedRestrictionGeneral ((sheafCompose (ProEt.topology Y)
        (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj R) U ⋙ target
  equation (P : DerivedCategory (proEtaleRingModules Y R)) :
    (ringedDerivedRestrictionGeneral ((sheafCompose (ProEt.topology Y)
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj R) U).map
        (proEtaleProjectionFormulaMate f R S c a b E P) ≫
      targetComparison.hom.app P =
    sourceComparison.hom.app P ≫ mate.app
      ((ringedDerivedRestrictionGeneral ((sheafCompose (ProEt.topology Y)
        (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj R) U).obj P)

private def fixedRestrictionIso
    {C D : Type*} [Category* C] [Category* D]
    (T : C × C ⥤ C) (T' : D × D ⥤ D) (r : C ⥤ D)
    (t : T ⋙ r ≅ (r.prod r) ⋙ T') (E : C) :
    (Functor.curryObj T).obj E ⋙ r ≅ r ⋙ (Functor.curryObj T').obj (r.obj E) :=
  NatIso.ofComponents (fun P ↦ t.app (E, P)) (by
    intro P Q h
    change r.map (T.map (Prod.mkHom (𝟙 E) h)) ≫ t.hom.app (E, Q) =
      t.hom.app (E, P) ≫ T'.map (Prod.mkHom (𝟙 (r.obj E)) (r.map h))
    have ht := t.hom.naturality (Prod.mkHom (𝟙 E) h)
    change r.map (T.map (Prod.mkHom (𝟙 E) h)) ≫ t.hom.app (E, Q) =
      t.hom.app (E, P) ≫ T'.map (Prod.mkHom (r.map (𝟙 E)) (r.map h)) at ht
    rw [r.map_id] at ht
    exact ht)

private def sliceSourceComparison
    {g : ProjectionRestriction.Global f R S c} {U : Y.ProEt}
    (l : ProjectionRestriction.Local f R S c g U) :
    (Functor.curryObj g.tensorY.functor).obj (g.operation.right.obj E) ⋙
        l.restrictionY.model.functor ≅
      l.restrictionY.model.functor ⋙ (Functor.curry.obj l.tensorY.functor).obj
        (l.operation.right.obj (l.restrictionX.model.functor.obj E)) := by
  letI := l.restrictionYAdditive
  letI := l.restrictionXAdditive
  exact fixedRestrictionIso _ _ _ l.restrictionTensorY.comparison _ ≪≫
    Functor.isoWhiskerLeft l.restrictionY.model.functor
      ((Functor.curry.obj l.tensorY.functor).mapIso (l.directImage.app E))

private def sliceTargetComparison
    {g : ProjectionRestriction.Global f R S c} {U : Y.ProEt}
    (l : ProjectionRestriction.Local f R S c g U) :
    (g.operation.left ⋙ (Functor.curryObj g.tensorX.functor).obj E ⋙
        g.operation.right) ⋙ l.restrictionY.model.functor ≅
      l.restrictionY.model.functor ⋙ (l.operation.left ⋙
        (Functor.curry.obj l.tensorX.functor).obj
          (l.restrictionX.model.functor.obj E) ⋙ l.operation.right) := by
  letI := l.restrictionYAdditive
  letI := l.restrictionXAdditive
  exact Functor.isoWhiskerLeft
      (g.operation.left ⋙ (Functor.curryObj g.tensorX.functor).obj E) l.directImage ≪≫
    Functor.isoWhiskerRight
      (Functor.isoWhiskerLeft g.operation.left
        (fixedRestrictionIso _ _ _ l.restrictionTensorX.comparison E)) l.operation.right ≪≫
    Functor.isoWhiskerRight l.pullback
      ((Functor.curry.obj l.tensorX.functor).obj
        (l.restrictionX.model.functor.obj E) ⋙ l.operation.right)

private def operationMate
    {C D : Type (u + 1)} [Category.{u} C] [Category.{u} D]
    [EssentiallySmall.{u + 1} C] [EssentiallySmall.{u + 1} D]
    {J : GrothendieckTopology C} {K : GrothendieckTopology D}
    {F : C ⥤ D} {R' : Sheaf J CommRingCat.{u + 1}}
    {S' : Sheaf K CommRingCat.{u + 1}}
    (o : ProjectionRestriction.Operation F R' S')
    (a' : ProjectionRestriction.TensorModel R') (b' : ProjectionRestriction.TensorModel S')
    (t : a'.functor ⋙ o.left ≅ (o.left.prod o.left) ⋙ b'.functor)
    (E' : ProjectionRestriction.Der S') :
    (Functor.curry.obj a'.functor).obj (o.right.obj E') ⟶
      o.left ⋙ (Functor.curry.obj b'.functor).obj E' ⋙ o.right :=
  let A := (Functor.curry.obj a'.functor).obj (o.right.obj E')
  let beta := (fixedRestrictionIso a'.functor b'.functor o.left t (o.right.obj E')).hom ≫
      Functor.whiskerLeft o.left
        ((Functor.curry.obj b'.functor).map (o.derivedAdjunction.counit.app E'))
  A.rightUnitor.inv ≫ Functor.whiskerLeft A o.derivedAdjunction.unit ≫
    (Functor.associator _ _ _).inv ≫ Functor.whiskerRight beta o.right ≫
      (Functor.associator o.left ((Functor.curry.obj b'.functor).obj E') o.right).hom

private theorem operationMate_eq
    {C D : Type (u + 1)} [Category.{u} C] [Category.{u} D]
    [EssentiallySmall.{u + 1} C] [EssentiallySmall.{u + 1} D]
    {J : GrothendieckTopology C} {K : GrothendieckTopology D}
    {F : C ⥤ D} {R' : Sheaf J CommRingCat.{u + 1}}
    {S' : Sheaf K CommRingCat.{u + 1}}
    (o : ProjectionRestriction.Operation F R' S')
    (a' : ProjectionRestriction.TensorModel R') (b' : ProjectionRestriction.TensorModel S')
    (t : a'.functor ⋙ o.left ≅ (o.left.prod o.left) ⋙ b'.functor)
    (E' : ProjectionRestriction.Der S') (P : ProjectionRestriction.Der R') :
    (operationMate o a' b' t E').app P =
      derivedProjectionFormulaMate o.left o.right o.derivedAdjunction
        a'.functor b'.functor t E' P := by
  simp [operationMate, fixedRestrictionIso, derivedProjectionFormulaMate,
    Adjunction.rightAdjointProjectionMap_app_app, Adjunction.homEquiv_unit,
    Functor.map_comp]

private theorem operationMate_commShift
    {C D : Type (u + 1)} [Category.{u} C] [Category.{u} D]
    [EssentiallySmall.{u + 1} C] [EssentiallySmall.{u + 1} D]
    {J : GrothendieckTopology C} {K : GrothendieckTopology D}
    {F : C ⥤ D} {R' : Sheaf J CommRingCat.{u + 1}}
    {S' : Sheaf K CommRingCat.{u + 1}}
    (o : ProjectionRestriction.Operation F R' S')
    [o.right.CommShift ℤ] [o.derivedAdjunction.CommShift ℤ]
    (a' : ProjectionRestriction.TensorModel R') (b' : ProjectionRestriction.TensorModel S')
    [sa : ProjectionRestriction.TensorShifts a'] [sb : ProjectionRestriction.TensorShifts b']
    (mu : o.OrdinaryTensor)
    (t : ProjectionRestriction.TensorComparison o.pullback o.leftModel a' b' mu.iso)
    (hs : ProjectionRestriction.TensorComparisonShifts t)
    (E' : ProjectionRestriction.Der S') :
    NatTrans.CommShift (operationMate o a' b' t.comparison E') ℤ := by
  let A := (Functor.curry.obj a'.functor).obj (o.right.obj E')
  let m : A ⋙ o.left ⟶ o.left ⋙
      (Functor.curry.obj b'.functor).obj (o.left.obj (o.right.obj E')) :=
    (fixedRestrictionIso a'.functor b'.functor o.left t.comparison (o.right.obj E')).hom
  have : NatTrans.CommShift m ℤ := by
    constructor
    intro n
    ext P
    simpa only [m, A, fixedRestrictionIso, NatIso.ofComponents_hom_app, Iso.app_hom,
      NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app,
      Functor.commShiftIso_comp_hom_app, Functor.comp_obj,
      Functor.curry_obj_obj_map, Functor.curry_obj_obj_obj, Category.assoc] using
      (hs.second (o.right.obj E') P n).symm
  let beta : A ⋙ o.left ⟶ o.left ⋙ (Functor.curry.obj b'.functor).obj E' :=
    m ≫ Functor.whiskerLeft o.left
      ((Functor.curry.obj b'.functor).map (o.derivedAdjunction.counit.app E'))
  have : NatTrans.CommShift beta ℤ := by dsimp only [beta]; infer_instance
  change NatTrans.CommShift (A.rightUnitor.inv ≫
    Functor.whiskerLeft A o.derivedAdjunction.unit ≫
    (Functor.associator _ _ _).inv ≫ Functor.whiskerRight beta o.right ≫
      (Functor.associator o.left ((Functor.curry.obj b'.functor).obj E') o.right).hom) ℤ
  infer_instance

/-- The projection mate has an exact presentation on every ordinary slice. -/
theorem proEtaleProjectionMateSlicePresentation (U : Y.ProEt) :
    Nonempty (ProEtaleProjectionMateSlicePresentation f R S c a b E U) := by
  classical
  obtain ⟨g, data, hprojection, _⟩ := ringedProjectionRestriction f R S c
  let l := data U
  obtain ⟨s, t, hmodel⟩ := proEtaleProjectionGlobalComparison f R S c a b g E
  let := l.tensorYShifts
  let := l.tensorXShifts
  let : (Functor.curry.obj l.tensorY.functor).CommShift₂Int := l.tensorYShifts.shifts
  let : (Functor.curry.obj l.tensorX.functor).CommShift₂Int := l.tensorXShifts.shifts
  let := l.restrictionYAdditive
  let := l.restrictionXAdditive
  let := l.operation.derivedAdjunction.rightAdjointCommShift ℤ
  have := l.operation.derivedAdjunction.commShift_of_leftAdjoint ℤ
  let : l.operation.left.IsTriangulated :=
    inferInstanceAs l.operation.pullback.mapDerivedCategory.IsTriangulated
  let : l.operation.right.IsTriangulated :=
    l.operation.derivedAdjunction.isTriangulated_rightAdjoint
  let := ProjectionRestriction.ringedProjectionTensorExact l.tensorY
    (l.operation.right.obj (l.restrictionX.model.functor.obj E))
  let := ProjectionRestriction.ringedProjectionTensorExact l.tensorX
    (l.restrictionX.model.functor.obj E)
  let tau := operationMate l.operation l.tensorY l.tensorX l.tensorComparison.comparison
    (l.restrictionX.model.functor.obj E)
  have htau := operationMate_eq l.operation l.tensorY l.tensorX l.tensorComparison.comparison
    (l.restrictionX.model.functor.obj E)
  have hshift : NatTrans.CommShift tau ℤ :=
    operationMate_commShift l.operation l.tensorY l.tensorX l.ordinaryTensor
      l.tensorComparison l.tensorComparison_shifts (l.restrictionX.model.functor.obj E)
  refine ⟨{
    source := (Functor.curry.obj l.tensorY.functor).obj
      (l.operation.right.obj (l.restrictionX.model.functor.obj E))
    target := l.operation.left ⋙ (Functor.curry.obj l.tensorX.functor).obj
      (l.restrictionX.model.functor.obj E) ⋙ l.operation.right
    sourceShift := inferInstanceAs
      (((Functor.curry.obj l.tensorY.functor).obj
        (l.operation.right.obj (l.restrictionX.model.functor.obj E))).CommShift ℤ)
    targetShift := inferInstanceAs
      ((l.operation.left ⋙ (Functor.curry.obj l.tensorX.functor).obj
        (l.restrictionX.model.functor.obj E) ⋙ l.operation.right).CommShift ℤ)
    sourceExact := inferInstance
    targetExact := inferInstance
    mate := tau
    shiftCompatible := hshift
    sourceComparison := Functor.isoWhiskerRight s l.restrictionY.model.functor ≪≫
      sliceSourceComparison f R S c E l
    targetComparison := Functor.isoWhiskerRight t l.restrictionY.model.functor ≪≫
      sliceTargetComparison f R S c E l
    equation := ?_ }⟩
  intro P
  have hcalc : l.restrictionY.model.functor.map
      (proEtaleProjectionFormulaMate f R S c a b E P) ≫
        (l.restrictionY.model.functor.map (t.hom.app P) ≫ (l.targetIso E P).hom) =
    (l.restrictionY.model.functor.map (s.hom.app P) ≫ (l.sourceIso E P).hom) ≫
      tau.app (l.restrictionY.model.functor.obj P) := by
    rw [← Category.assoc, ← Functor.map_comp, hmodel, Functor.map_comp, Category.assoc,
      htau]
    simpa only [Category.assoc] using
      congrArg (fun k ↦ l.restrictionY.model.functor.map (s.hom.app P) ≫ k)
      (hprojection U E P)
  simpa only [sliceSourceComparison, sliceTargetComparison, fixedRestrictionIso,
    ProjectionRestriction.Local.sourceIso, ProjectionRestriction.Local.targetIso,
    Iso.trans_hom, NatTrans.comp_app, Functor.isoWhiskerRight_hom,
    Functor.isoWhiskerLeft_hom, Functor.whiskerRight_app, Functor.whiskerLeft_app,
    NatIso.ofComponents_hom_app, Functor.mapIso_hom, Iso.app_hom, Iso.prod_hom,
    Iso.refl_hom, Functor.comp_obj, Functor.comp_map, Functor.curry_map_app_app,
    Functor.curry_obj_obj_obj, Functor.curry_obj_obj_map, Functor.curry_obj_map_app,
    Functor.curryObj, ringedDerivedRestrictionGeneral,
    Functor.map_comp, Category.assoc] using hcalc
end AlgebraicGeometry.Scheme
