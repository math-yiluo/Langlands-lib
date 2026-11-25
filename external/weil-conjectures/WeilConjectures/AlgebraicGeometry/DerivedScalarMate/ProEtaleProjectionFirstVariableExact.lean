/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.DerivedScalarMate.DerivedScalarMateData
import all WeilConjectures.AlgebraicGeometry.ProjectionRestriction.RingedProjectionGlobalModel
import all WeilConjectures.AlgebraicGeometry.ProEtale.Projection.ProEtaleProjectionGlobalComparison
import all WeilConjectures.AlgebraicGeometry.ProjectionRestriction.RingedProjectionTensorShifts
import WeilConjectures.AlgebraicGeometry.ProjectionRestriction.RingedProjectionTensorModelIso
import WeilConjectures.AlgebraicGeometry.ProjectionRestriction.RingedProjectionTensorComparison
import WeilConjectures.AlgebraicGeometry.ProEtale.Tensor.ProEtaleTensorComparisonTransport
import WeilConjectures.Mathlib.CategoryTheory.Shift.CommShift
import WeilConjectures.CategoryTheory.DerivedCategory.Shift.ExactFunctor
import WeilConjectures.CategoryTheory.Adjunction.ProjectionMapShift
import Mathlib.CategoryTheory.Triangulated.Adjunction

/-!
# Exactness and first-variable shifts of the pro-etale projection mate

Source: Stacks Project, Cohomology on Sites, Tags 0B56 and 07A4;
Derived Categories, Tag 0A8D.
(blueprint: lem-sfb-proetale-projection-first-variable-exact).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
namespace AlgebraicGeometry.Scheme.DerivedScalarMate

open ProjectionRestriction

attribute [local implicit_reducible] resolving proEtaleFlatRepresentatives
  CategoryTheory.Functor.map₂HomologicalComplex Operation.left
attribute [local irreducible] SheafOfModules.monoidalCategory
  SheafOfModules.siteDerivedTensorIndependentCoefficients
  HomologicalComplex₂.total MorphismProperty.Q'
  SheafOfModules.KFlatFixedTensor.representativeIso
  CategoryTheory.Functor.leftAdjoint CategoryTheory.presheafToSheaf
  proEtaleOrdinaryTensorPullback
attribute [local semireducible] ObjectProperty.hasShift ObjectProperty.commShiftι

private abbrev nativeModel {W : Scheme.{u}}
    {R : Sheaf (ProEt.topology W) CommRingCat.{u + 1}}
    (a : ProEtaleTensorModel W R) (b : TensorModel R) : TensorModel R where
  preadditive := b.preadditive
  functor := a.tensor
  representative := a.representative
  descent := b.descent

private abbrev nativeModelShifts {W : Scheme.{u}}
    {R : Sheaf (ProEt.topology W) CommRingCat.{u + 1}}
    (a : ProEtaleTensorModel W R) (b : TensorModel R)
    [s : (Functor.curryObj a.tensor).CommShift₂Int]
    (ha : CanonicalTensorShifts a) : TensorShifts (nativeModel a b) := by
  let : MonoidalCategory (Mod R) := SheafOfModules.monoidalCategory R
  let := b.preadditive
  refine {
    shifts := s
    tensorAdditive := inferInstance
    tensorObjAdditive := fun _ ↦ inferInstance
    first := ?_
    second := ?_ }
  · intro P Q hp hq n
    let hpn := ha.1 P n hp
    refine ⟨hpn, ?_⟩
    have h := congrArg (fun f ↦ f ≫ (shiftFunctor (Der R) n).map
      (a.representative.inv.app (⟨P, hp⟩, ⟨Q, hq⟩))) (ha.2.1 P Q hp hq n hpn)
    simp only [Category.assoc, ← CategoryTheory.Functor.map_comp,
      Iso.app_hom, Iso.hom_inv_id_app] at h
    erw [CategoryTheory.Functor.map_id, Category.comp_id] at h
    exact h
  · intro P Q hp hq n
    let hqn := ha.1 Q n hq
    refine ⟨hqn, ?_⟩
    have h := congrArg (fun f ↦ f ≫ (shiftFunctor (Der R) n).map
      (a.representative.inv.app (⟨P, hp⟩, ⟨Q, hq⟩))) (ha.2.2 P Q hp hq n hqn)
    simp only [Category.assoc, ← CategoryTheory.Functor.map_comp,
      Iso.app_hom, Iso.hom_inv_id_app] at h
    erw [CategoryTheory.Functor.map_id, Category.comp_id] at h
    exact h

private theorem resolvingFlipExact {W : Scheme.{u}}
    {R : Sheaf (ProEt.topology W) CommRingCat.{u + 1}}
    (a : TensorModel R) [sa : TensorShifts a]
    (P : CochainComplex (Mod R) ℤ) (hp : resolving R P) :
    ((Functor.curry.obj a.functor).flip.obj (DerivedCategory.Q.obj P)).IsTriangulated := by
  let := sa.tensorAdditive
  let := sa.tensorObjAdditive
  let := resolving_stable a
  let := resolving_essSurj (R := R)
  obtain ⟨e, he⟩ := ringedProjectionTensorModelIso a
  obtain ⟨s, hs⟩ := SheafOfModules.KFlatFixedTensor.kFlat_fixed_tensor_triangulated R
  let := s
  have hf := hs P hp.1 hp.2
  have := hf.2.2.1.2
  obtain ⟨c, hc, hn⟩ := hf.2.2.2.2.1
  let := hc
  let q := (resolving R).ι ⋙ DerivedCategory.Q
  let eP : (SheafOfModules.KFlatFixedTensor.derivedTensor R).flip.obj
      (DerivedCategory.Q.obj P) ≅
      (Functor.curry.obj a.functor).flip.obj (DerivedCategory.Q.obj P) :=
    ((flipFunctor _ _ _).mapIso (Functor.curry.mapIso e)).app (DerivedCategory.Q.obj P)
  let cP := Functor.isoWhiskerLeft (resolving R).ι c ≪≫
    (Functor.associator (resolving R).ι DerivedCategory.Q
      ((SheafOfModules.KFlatFixedTensor.derivedTensor R).flip.obj
        (DerivedCategory.Q.obj P))).symm
  let rP := representativeFirst a ⟨P, hp⟩
  have hr : NatTrans.CommShift rP.hom ℤ := representativeFirst_shift a ⟨P, hp⟩
  have hcomp : Functor.whiskerLeft q eP.hom = cP.inv ≫ rP.hom := by
    apply (cancel_epi cP.hom).1
    simp only [← Category.assoc, Iso.hom_inv_id, Category.id_comp]
    ext Q
    simp only [cP, Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app,
      Functor.associator_inv_app, Category.comp_id]
    change c.hom.app Q.obj ≫ e.hom.app
      (DerivedCategory.Q.obj Q.obj, DerivedCategory.Q.obj P) =
        a.representative.hom.app (Q, ⟨P, hp⟩)
    rw [show c.hom.app Q.obj =
      (SheafOfModules.KFlatFixedTensor.representativeIso R Q.obj P
        Q.property.1 hp.1 Q.property.2 hp.2).hom from
      congrArg Iso.hom (hn Q.obj Q.property.1 Q.property.2)]
    exact he Q.obj P Q.property hp
  have hcP : NatTrans.CommShift cP.inv ℤ := by
    dsimp only [cP, Iso.trans_inv, Iso.symm_inv, Functor.isoWhiskerLeft_inv]
    infer_instance
  have : NatTrans.CommShift (Functor.whiskerLeft q eP.hom) ℤ := by
    rw [hcomp]
    infer_instance
  have : NatTrans.CommShift eP.hom ℤ :=
    NatTrans.CommShift.of_whiskerLeft eP.hom q (fun E ↦
      ⟨q.objPreimage E, (q.objObjPreimageIso E).inv, inferInstance⟩)
  exact Functor.isTriangulated_of_iso eP

private theorem nativeFirstExact {W : Scheme.{u}}
    {R : Sheaf (ProEt.topology W) CommRingCat.{u + 1}}
    (a : ProEtaleTensorModel W R) [s : (Functor.curryObj a.tensor).CommShift₂Int]
    (ha : CanonicalTensorShifts a) (E : DerivedCategory (proEtaleRingModules W R)) :
    ((Functor.curryObj a.tensor).flip.obj E).IsTriangulated := by
  obtain ⟨b, _⟩ := tensorModelWithShifts_nonempty R
  let m := nativeModel a b
  let sa := nativeModelShifts a b ha
  let := sa
  let : (Functor.curry.obj m.functor).CommShift₂Int := sa.shifts
  let := resolving_essSurj (R := R)
  let q := (resolving R).ι ⋙ DerivedCategory.Q
  let P := q.objPreimage E
  let e := q.objObjPreimageIso E
  let : ((Functor.curry.obj m.functor).flip.obj (q.obj P)).IsTriangulated :=
    resolvingFlipExact m P.obj P.property
  have : NatTrans.CommShift ((Functor.curry.obj m.functor).flip.mapIso e).hom ℤ :=
    sa.shifts.commShift_flip_map e.hom
  exact Functor.isTriangulated_of_iso ((Functor.curry.obj m.functor).flip.mapIso e)

private def firstComparison {C D : Type*} [Category C] [Category D]
    (L : C ⥤ D) (T : C × C ⥤ C) (S : D × D ⥤ D)
    (c : T ⋙ L ⟶ (L.prod L) ⋙ S) (P : C) :
    (Functor.curryObj T).flip.obj P ⋙ L ⟶
      L ⋙ (Functor.curryObj S).flip.obj (L.obj P) where
  app M := c.app (M, P)
  naturality {M M'} f := by
    have h := c.naturality (Prod.mkHom f (𝟙 P))
    simpa only [Functor.comp_map, Functor.prod_map, CategoryTheory.Functor.map_id,
      Functor.curryObj, Functor.flip_obj_map, Functor.curry_obj_map_app,
      Functor.curry_obj_obj_map]
      using h

private theorem firstComparisonTransport
    {C D : Type*} [Category C] [Category D] [HasShift C ℤ] [HasShift D ℤ]
    [Preadditive C] [Preadditive D]
    [∀ k : ℤ, (shiftFunctor C k).Additive] [∀ k : ℤ, (shiftFunctor D k).Additive]
    (T : C × C ⥤ C) (S : D × D ⥤ D)
    [(Functor.curryObj T).CommShift₂Int] [(Functor.curryObj S).CommShift₂Int]
    (L K : C ⥤ D) [L.CommShift ℤ] [K.CommShift ℤ] (e : K ≅ L)
    [NatTrans.CommShift e.hom ℤ]
    (c : T ⋙ L ≅ (L.prod L) ⋙ S) (d : T ⋙ K ≅ (K.prod K) ⋙ S)
    (hd : ∀ U V, e.hom.app (T.obj (U, V)) ≫ c.hom.app (U, V) =
      d.hom.app (U, V) ≫ S.map (Prod.mkHom (e.hom.app U) (e.hom.app V))) (P : C)
    [NatTrans.CommShift (firstComparison K T S d.hom P) ℤ] :
    NatTrans.CommShift (firstComparison L T S c.hom P) ℤ := by
  let tau :=
    (Functor.isoWhiskerLeft ((Functor.curryObj T).flip.obj P) e.symm).hom ≫
      firstComparison K T S d.hom P ≫
      (Functor.isoWhiskerRight e ((Functor.curryObj S).flip.obj (K.obj P))).hom ≫
      Functor.whiskerLeft L ((Functor.curryObj S).flip.map (e.hom.app P))
  have ht : NatTrans.CommShift tau ℤ := by
    dsimp only [tau, Functor.isoWhiskerLeft_hom, Iso.symm_hom,
      Functor.isoWhiskerRight_hom]
    infer_instance
  have heq : firstComparison L T S c.hom P = tau := by
    ext U
    change c.hom.app (U, P) = e.inv.app (T.obj (U, P)) ≫
      d.hom.app (U, P) ≫ S.map (Prod.mkHom (e.hom.app U) (𝟙 _)) ≫
        S.map (Prod.mkHom (𝟙 _) (e.hom.app P))
    apply (cancel_epi (e.hom.app (T.obj (U, P)))).1
    simpa only [Category.assoc, Iso.hom_inv_id_app_assoc,
      ← S.map_comp, CategoryTheory.prod_comp, Category.id_comp, Category.comp_id]
      using hd U P
  exact heq ▸ ht

private theorem nativeComparisonShift
    {Z T : Scheme.{u}} (f : Z ⟶ T)
    (A : Sheaf (ProEt.topology T) CommRingCat.{u + 1})
    (t : ProEtaleTensorModel T A) (z : ProEtaleTensorModel Z (inverseRing f A))
    [(Functor.curryObj t.tensor).CommShift₂Int]
    [(Functor.curryObj z.tensor).CommShift₂Int]
    (ht : CanonicalTensorShifts t) (hz : CanonicalTensorShifts z)
    (P : DerivedCategory (proEtaleRingModules T A)) :
    NatTrans.CommShift (firstComparison (pull f A) t.tensor z.tensor
      (proEtaleCanonicalTensorComparison f A (inverseRing f A) (Iso.refl _) t z).hom P)
      ℤ := by
  obtain ⟨bT, _⟩ := tensorModelWithShifts_nonempty A
  obtain ⟨bZ, _⟩ := tensorModelWithShifts_nonempty (inverseRing f A)
  let m := nativeModel t bT
  let n := nativeModel z bZ
  let sm := nativeModelShifts t bT ht
  let sn := nativeModelShifts z bZ hz
  let := sm
  let := sn
  let : (Functor.curry.obj m.functor).CommShift₂Int := sm.shifts
  let : (Functor.curry.obj n.functor).CommShift₂Int := sn.shifts
  let o := globalOperation f A (inverseRing f A) (Iso.refl _)
  let mu := globalOrdinaryTensor f A (inverseRing f A) (Iso.refl _)
  obtain ⟨tc, hc⟩ := globalTensorComparison_exists f A (inverseRing f A)
    (Iso.refl _) o rfl m n sm sn mu
  let e := o.moduleAdjunction.leftAdjointUniq
    (proEtaleRingModuleAdjunction f A (inverseRing f A) (Iso.refl _))
  let l := Functor.mapDerivedCategoryNatIso e
  have hl : NatTrans.CommShift l.hom ℤ := by
    dsimp only [l]
    infer_instance
  let := hl
  have hd (U V : DerivedCategory (proEtaleRingModules T A)) :
      l.hom.app (t.tensor.obj (U, V)) ≫
          (proEtaleCanonicalTensorComparison f A (inverseRing f A) (Iso.refl _) t z).hom.app
            (U, V) =
        tc.comparison.hom.app (U, V) ≫
          z.tensor.map (Prod.mkHom (l.hom.app U) (l.hom.app V)) := by
    have h := proEtaleTensorComparisonTransport f A (inverseRing f A) (Iso.refl _)
      o.pullback e o.leftModel l (fun C ↦ Functor.mapDerivedCategoryNatIso_fac e C)
      t z m n mu.iso tc (globalOrdinary_square f A (inverseRing f A) (Iso.refl _))
      (Iso.refl _) (Iso.refl _) (by simp [m, nativeModel]; rfl)
      (by simp [n, nativeModel]; rfl) U V
    simp only [Iso.refl_hom, NatTrans.id_app] at h
    erw [CategoryTheory.Functor.map_id, Category.id_comp, Category.comp_id] at h
    exact h
  have htc : NatTrans.CommShift (firstComparison o.left t.tensor z.tensor
      tc.comparison.hom P) ℤ := by
    constructor
    intro k
    ext U
    convert (hc.first U P k).symm using 1 <;>
      simp only [firstComparison, NatTrans.comp_app, Functor.whiskerRight_app,
        Functor.whiskerLeft_app, Functor.commShiftIso_comp_hom_app,
        Functor.flip_obj_map, Category.assoc]
    all_goals rfl
  let := htc
  exact firstComparisonTransport t.tensor z.tensor (pull f A) o.left l _ _ hd P

/-- The native projection arrow is a transformation of exact functors of its
first input. Source: Stacks 0B56, 07A4, 0A8D; the first-variable calculation of
`ringedProjectionFirstShift`, for the original pro-etale site universes
(blueprint: lem-sfb-proetale-projection-first-variable-exact).

Proof: resolve tensor inputs by flat-term K-flat complexes. Tensoring with a fixed
such complex preserves acyclic complexes and sends the standard cone triangle to
the cone triangle of its total tensor map: the unshifted summands have identity
comparison and the shifted summands have the total-complex sign. Localization
therefore makes tensoring in the first variable exact. The normalization hypotheses
identify its shift with this cone-compatible shift on representatives, and resolving
descent identifies it on every derived object. Exact pullback has its termwise shift;
the compatible right adjoint shift makes direct image exact by the triangulated
adjunction theorem. Composition proves exactness of the two displayed functors.

Curry the canonical pullback/tensor comparison and fix the second argument P.
Its first-variable shift square is checked on flat K-flat representatives: the
ordinary pullback/tensor comparison preserves each total summand, and the first
shift has no additional Koszul sign. The representative equations for the tensor
models and the exact-pullback factorization give this square after localization;
fully faithful resolving restriction extends it to arbitrary derived inputs.
Form the natural projection transformation by the adjunction unit, this tensor
comparison, and the counit tensored with the identity of pullback(P). Naturality
of these maps and their shift squares prove CommShift by composition and whiskering
(the abstract lemma `Adjunction.commShift_rightAdjointProjectionMapFlipApp`).
Its component is precisely the adjoint-of-counit definition of the displayed
projection arrow. This argument never asserts that the projection arrow is an
isomorphism. -/
theorem proEtale_projection_first_variable_exact
    {Z T : Scheme.{u}} (f : Z ⟶ T)
    (A : Sheaf (ProEt.topology T) CommRingCat.{u + 1})
    (t : ProEtaleTensorModel T A) (z : ProEtaleTensorModel Z (inverseRing f A))
    [(Functor.curryObj t.tensor).CommShift₂Int]
    [(Functor.curryObj z.tensor).CommShift₂Int]
    [(push f A).CommShift ℤ] [(adjunction f A).CommShift ℤ]
    (ht : CanonicalTensorShifts t) (hz : CanonicalTensorShifts z)
    (P : DerivedCategory (proEtaleRingModules T A)) :
    (push f A ⋙ (Functor.curryObj t.tensor).flip.obj P).IsTriangulated ∧
    ((Functor.curryObj z.tensor).flip.obj ((pull f A).obj P) ⋙
      push f A).IsTriangulated ∧
    ∃ pi : push f A ⋙ (Functor.curryObj t.tensor).flip.obj P ⟶
        (Functor.curryObj z.tensor).flip.obj ((pull f A).obj P) ⋙ push f A,
      (∀ K, pi.app K =
        proEtaleProjectionFormulaMate f A (inverseRing f A) (Iso.refl _) t z K P) ∧
      NatTrans.CommShift pi ℤ := by
  let : ((Functor.curryObj t.tensor).flip.obj P).IsTriangulated := nativeFirstExact t ht P
  let : ((Functor.curryObj z.tensor).flip.obj ((pull f A).obj P)).IsTriangulated :=
    nativeFirstExact z hz ((pull f A).obj P)
  let : (pull f A).IsTriangulated :=
    inferInstanceAs (proEtaleRingModulePullback f A (inverseRing f A)
      (Iso.refl _)).mapDerivedCategory.IsTriangulated
  let : (push f A).IsTriangulated := (adjunction f A).isTriangulated_rightAdjoint
  let phi : (Functor.postcompose₂.obj (pull f A)).obj (Functor.curryObj t.tensor) ⟶
      (((Functor.whiskeringLeft₂ _).obj (pull f A)).obj (pull f A)).obj
        (Functor.curryObj z.tensor) :=
    Functor.curry.map
      (proEtaleCanonicalTensorComparison f A (inverseRing f A) (Iso.refl _) t z).hom ≫
      (Functor.curryObjProdComp (pull f A) (pull f A) z.tensor).hom
  let pi := (adjunction f A).rightAdjointProjectionMapFlipApp
    (T_C := Functor.curryObj z.tensor) (T_D := Functor.curryObj t.tensor) phi P
  have hphi : NatTrans.CommShift (Adjunction.comparisonFlipApp phi P) ℤ := by
    have heq : Adjunction.comparisonFlipApp phi P =
        firstComparison (pull f A) t.tensor z.tensor
          (proEtaleCanonicalTensorComparison f A (inverseRing f A) (Iso.refl _) t z).hom
          P := by
      ext U
      exact Category.comp_id _
    rw [heq]
    exact nativeComparisonShift f A t z ht hz P
  let := hphi
  refine ⟨inferInstance, inferInstance, pi, ?_, ?_⟩
  · intro K
    dsimp [pi, phi, Adjunction.rightAdjointProjectionMapFlipApp,
      proEtaleProjectionFormulaMate, derivedProjectionFormulaMate]
  · exact Adjunction.commShift_rightAdjointProjectionMapFlipApp (adjunction f A) phi ℤ P

end AlgebraicGeometry.Scheme.DerivedScalarMate
