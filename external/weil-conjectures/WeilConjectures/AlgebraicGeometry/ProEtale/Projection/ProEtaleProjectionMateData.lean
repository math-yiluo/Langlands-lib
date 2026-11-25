/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.CategoryTheory.Projection.ProjectionFormulaBaseChangeNaturality
public import Mathlib.CategoryTheory.Triangulated.Functor
import WeilConjectures.AlgebraicGeometry.ProjectionRestriction.RingedProjectionGlobalModel
import WeilConjectures.AlgebraicGeometry.ProEtale.Projection.ProEtaleProjectionGlobalComparison
import WeilConjectures.AlgebraicGeometry.ProjectionRestriction.RingedProjectionTensorExact
import WeilConjectures.AlgebraicGeometry.SignedProjectionResolution.SignedProjectionResolutionNormalization
import Mathlib.CategoryTheory.Triangulated.Adjunction

/-!
# Natural transformation and unit normalization of the pro-etale projection mate

The shifts are constructed together with the mate, by transport from the normalized
model. Arbitrary independently chosen shift structures do not suffice.

## References

* Stacks, Cohomology on Sites, Tags 06YU, 07A4, 07A6 and 0B56
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
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

private theorem unit_isIso :
    IsIso (proEtaleProjectionFormulaMate f R S c a b E
      ((DerivedCategory.singleFunctor (proEtaleRingModules Y R) 0).obj
        (SheafOfModules.unit ((sheafCompose (ProEt.topology Y)
          (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj R)))) := by
  classical
  let A := proEtaleRingModules Y R
  let U : A := SheafOfModules.unit ((sheafCompose (ProEt.topology Y)
    (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj R)
  let F := (HomologicalComplex.single A (.up ℤ) 0).obj U
  let z : F.X 0 ≅ ∏ᶜ (fun _ : Fin 1 ↦ U) :=
    HomologicalComplex.singleObjXSelf (.up ℤ) 0 U ≪≫ (productUniqueIso (fun _ : Fin 1 ↦ U)).symm
  let pkg : SheafOfModules.StrictPerfectCoefficientPackageOnSite
      ((sheafCompose (ProEt.topology Y)
        (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj R) F :=
    { N := fun _ ↦ 1
      i := fun n ↦ if h : n = 0 then eqToHom (congrArg F.X h) ≫ z.hom else 0
      p := fun n ↦ if h : n = 0 then z.inv ≫ eqToHom (congrArg F.X h.symm) else 0
      splitting := by
        intro n
        by_cases h : n = 0
        · subst n
          simp only [dite_true, eqToHom_refl, Category.id_comp, Category.comp_id,
            Iso.hom_inv_id]
        · exact (HomologicalComplex.isZero_single_obj_X (.up ℤ) 0 U n h).eq_of_src _ _ }
  have hb : ∃ l h : ℤ, ∀ n : ℤ, n < l ∨ h < n → IsZero (F.X n) := by
    refine ⟨0, 0, ?_⟩
    intro n hn
    exact HomologicalComplex.isZero_single_obj_X (.up ℤ) 0 U n (by omega)
  obtain ⟨I, hI, ⟨e⟩⟩ := DerivedCategory.exists_iso_Q_obj_of_isKInjective E
  have h := SignedProjectionResolution.normalization f R S c a b E
    (DerivedCategory.Q.obj F) I hI e F (Iso.refl _) pkg hb
  exact ⟨⟨_, h.2.1, h.2.2⟩⟩

/-- The native projection mate has its prescribed components and is invertible at the
coefficient unit. There are compatible integer shifts making its two functors exact
and the mate shift-compatible. -/
theorem proEtaleProjectionMateData :
    ∃ (_sF : ((Functor.curryObj a.tensor).obj
      ((proEtaleRingDerivedDirectImage f R S c).obj E)).CommShift ℤ)
      (_sG : (proEtaleRingDerivedPullback f R S c ⋙
      (Functor.curryObj b.tensor).obj E ⋙
        proEtaleRingDerivedDirectImage f R S c).CommShift ℤ),
      ((Functor.curryObj a.tensor).obj
        ((proEtaleRingDerivedDirectImage f R S c).obj E)).IsTriangulated ∧
      (proEtaleRingDerivedPullback f R S c ⋙
        (Functor.curryObj b.tensor).obj E ⋙
          proEtaleRingDerivedDirectImage f R S c).IsTriangulated ∧
    ∃ τ : (Functor.curryObj a.tensor).obj
          ((proEtaleRingDerivedDirectImage f R S c).obj E) ⟶
        proEtaleRingDerivedPullback f R S c ⋙
          (Functor.curryObj b.tensor).obj E ⋙ proEtaleRingDerivedDirectImage f R S c,
        (∀ P, τ.app P = proEtaleProjectionFormulaMate f R S c a b E P) ∧
        NatTrans.CommShift τ ℤ ∧
        IsIso (τ.app ((DerivedCategory.singleFunctor (proEtaleRingModules Y R) 0).obj
          (SheafOfModules.unit ((sheafCompose (ProEt.topology Y)
            (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj R)))) := by
  classical
  obtain ⟨g⟩ := ProjectionRestriction.globalModel_exists f R S c
  obtain ⟨s, t, hmodel⟩ := proEtaleProjectionGlobalComparison f R S c a b g E
  let := g.tensorYShifts
  let := g.tensorXShifts
  let : (Functor.curry.obj g.tensorY.functor).CommShift₂Int := g.tensorYShifts.shifts
  let : (Functor.curry.obj g.tensorX.functor).CommShift₂Int := g.tensorXShifts.shifts
  let := g.operation.derivedAdjunction.rightAdjointCommShift ℤ
  let := g.operation.derivedAdjunction.commShift_of_leftAdjoint ℤ
  let : g.operation.left.IsTriangulated :=
    inferInstanceAs g.operation.pullback.mapDerivedCategory.IsTriangulated
  let : g.operation.right.IsTriangulated :=
    g.operation.derivedAdjunction.isTriangulated_rightAdjoint
  let := ProjectionRestriction.ringedProjectionTensorExact g.tensorY
    (g.operation.right.obj E)
  let := ProjectionRestriction.ringedProjectionTensorExact g.tensorX E
  let tau := operationMate g.operation g.tensorY g.tensorX g.tensorComparison.comparison E
  let : NatTrans.CommShift tau ℤ := operationMate_commShift g.operation
    g.tensorY g.tensorX g.ordinaryTensor g.tensorComparison g.tensorComparison_shifts E
  let : ((Functor.curryObj g.tensorY.functor).obj
      (g.operation.right.obj E)).CommShift ℤ :=
    inferInstanceAs (((Functor.curry.obj g.tensorY.functor).obj
      (g.operation.right.obj E)).CommShift ℤ)
  let : ((Functor.curryObj g.tensorX.functor).obj E).CommShift ℤ :=
    inferInstanceAs (((Functor.curry.obj g.tensorX.functor).obj E).CommShift ℤ)
  let : ((Functor.curryObj g.tensorY.functor).obj
      (g.operation.right.obj E)).IsTriangulated :=
    inferInstanceAs (((Functor.curry.obj g.tensorY.functor).obj
      (g.operation.right.obj E)).IsTriangulated)
  let : ((Functor.curryObj g.tensorX.functor).obj E).IsTriangulated :=
    inferInstanceAs (((Functor.curry.obj g.tensorX.functor).obj E).IsTriangulated)
  let : (g.operation.left ⋙ (Functor.curryObj g.tensorX.functor).obj E ⋙
      g.operation.right).IsTriangulated := inferInstance
  let sF := Functor.CommShift.ofIso s.symm ℤ
  let sG := Functor.CommShift.ofIso t.symm ℤ
  let := sF
  let := sG
  let : NatTrans.CommShift s.symm.hom ℤ :=
    Functor.CommShift.ofIso_compatibility s.symm ℤ
  let : NatTrans.CommShift s.hom ℤ := NatTrans.CommShift.of_iso_inv s.symm ℤ
  let : NatTrans.CommShift t.symm.hom ℤ :=
    Functor.CommShift.ofIso_compatibility t.symm ℤ
  let : NatTrans.CommShift t.inv ℤ := Functor.CommShift.ofIso_compatibility t.symm ℤ
  let native := s.hom ≫ tau ≫ t.inv
  have hnative (P) : native.app P = proEtaleProjectionFormulaMate f R S c a b E P := by
    apply (cancel_mono (t.hom.app P)).1
    change (s.hom.app P ≫ tau.app P ≫ t.inv.app P) ≫ t.hom.app P = _
    simp only [Category.assoc, Iso.inv_hom_id_app]
    erw [Category.comp_id]
    simpa only [tau, operationMate_eq] using (hmodel P).symm
  refine ⟨sF, sG, Functor.isTriangulated_of_iso s.symm,
    Functor.isTriangulated_of_iso t.symm, native, hnative, ?_, ?_⟩
  · dsimp only [native]
    infer_instance
  · rw [hnative]
    exact unit_isIso f R S c a b E
end AlgebraicGeometry.Scheme
