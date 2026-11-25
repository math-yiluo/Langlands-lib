/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.ProjectionRestriction.RingedProjectionRestrictionDataSupplement
public import Mathlib.CategoryTheory.Triangulated.Functor
import WeilConjectures.Algebra.Homology.KFlatFixedTensor.KFlatFixedTensorTriangulatedSupplement
import WeilConjectures.AlgebraicGeometry.ProjectionRestriction.RingedProjectionTensorModelIso
import WeilConjectures.Algebra.Homology.TensorColimitsIndependentCoefficients
import WeilConjectures.Algebra.Homology.KFlatIndependentCoefficients
import WeilConjectures.Algebra.Homology.KFlatCoefficientUniverse
import WeilConjectures.Algebra.Homology.SmoothPurity.KFlatSupplement
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Monoidal
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
import Mathlib.Algebra.Category.Grp.FilteredColimits
import Mathlib.Algebra.Homology.BifunctorShift
import Mathlib.Algebra.Homology.QuasiIso
import Mathlib.CategoryTheory.Sites.Equivalence
import Mathlib.CategoryTheory.Comma.StructuredArrow.Small
import Mathlib.CategoryTheory.Limits.EssentiallySmall
import WeilConjectures.FromJoel.CategoryTheory.Monoidal.KFlat
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
import Mathlib.CategoryTheory.Adjunction.FullyFaithfulLimits
import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor
import Mathlib.CategoryTheory.ObjectProperty.Shift
import WeilConjectures.Mathlib.CategoryTheory.Shift.CommShift

/-!
# Exactness of a representative-normalized fixed-factor tensor

## References

* Stacks Project, Tags 06YU and 07A4
* More on Algebra, Tag 0FNH
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option Elab.async false
universe u
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.Scheme.ProjectionRestriction

variable {C : Type (u + 1)} [Category.{u} C] [EssentiallySmall.{u + 1} C]
  {J : GrothendieckTopology C} {R : Sheaf J CommRingCat.{u + 1}}

attribute [local irreducible] SheafOfModules.monoidalCategory
  SheafOfModules.siteDerivedTensorIndependentCoefficients
  HomologicalComplex₂.total MorphismProperty.Q'
  SheafOfModules.KFlatFixedTensor.representativeIso

attribute [local semireducible] ObjectProperty.hasShift ObjectProperty.commShiftι

private theorem flatResolution (B : CochainComplex (Mod R) ℤ) :
    ∃ (P : CochainComplex (Mod R) ℤ) (f : P ⟶ B), resolving R P ∧ QuasiIso f := by
  obtain ⟨P, f, hp, hf, hq, _⟩ :=
    CochainComplex.exists_isKFlatResolutionIndependentCoefficients B
  refine ⟨P, f, ⟨hp, ?_⟩, hq⟩
  intro n
  exact (exactFunctor _ _).prop_of_iso
    (SheafOfModules.siteSheafTensorRightIso R (P.X n)).symm (hf n)

private theorem resolvingStable (a : TensorModel R) [sa : TensorShifts a] :
    (resolving R).IsStableUnderShift ℤ where
  isStableUnderShiftBy n := ⟨fun P hp ↦ (sa.second P P hp hp n).choose⟩

private theorem resolvingEssSurj : ((resolving R).ι ⋙ DerivedCategory.Q).EssSurj := by
  constructor
  intro E
  obtain ⟨P, f, hp, hf⟩ := flatResolution (DerivedCategory.Q.objPreimage E)
  let := hf
  exact ⟨⟨P, hp⟩, ⟨asIso (DerivedCategory.Q.map f) ≪≫
    DerivedCategory.Q.objObjPreimageIso E⟩⟩

-- The fixed-factor part of the supplied natural representative comparison.
private def representativeSecond (a : TensorModel R)
    (P : (resolving R).FullSubcategory) :
    (resolving R).ι ⋙ ((tensor R).map₂CochainComplex).obj P.obj ⋙ DerivedCategory.Q ≅
      ((resolving R).ι ⋙ DerivedCategory.Q) ⋙
        (Functor.curry.obj a.functor).obj (DerivedCategory.Q.obj P.obj) :=
  NatIso.ofComponents (fun Q ↦ a.representative.app (P, Q)) (fun {Q Q'} f ↦ by
    have h := a.representative.hom.naturality (Prod.mkHom (𝟙 P) f)
    change DerivedCategory.Q.map
      ((((tensor R).map₂CochainComplex).map (𝟙 P.obj)).app Q.obj ≫
        (((tensor R).map₂CochainComplex).obj P.obj).map f.hom) ≫ _ =
      _ ≫ a.functor.map (Prod.mkHom (DerivedCategory.Q.map (𝟙 P.obj))
        (DerivedCategory.Q.map f.hom)) at h
    erw [CategoryTheory.Functor.map_id, NatTrans.id_app, Category.id_comp,
      CategoryTheory.Functor.map_id] at h
    exact h)

private theorem inclusionShift [(resolving R).IsStableUnderShift ℤ]
    (Q : (resolving R).FullSubcategory) (n : ℤ) :
    ((resolving R).ι.commShiftIso n).hom.app Q = 𝟙 (Q.obj⟦n⟧) := rfl

private theorem representativeSecondShift (a : TensorModel R) [sa : TensorShifts a]
    [(resolving R).IsStableUnderShift ℤ] (P : (resolving R).FullSubcategory) :
    NatTrans.CommShift (representativeSecond a P).hom ℤ := by
  let := sa.tensorAdditive
  let := sa.tensorObjAdditive
  constructor
  intro n
  ext Q
  obtain ⟨hqn, h⟩ := sa.second P.obj Q.obj P.property Q.property n
  have hh := congrArg (fun f ↦ f ≫
    (shiftFunctor (Der R) n).map (a.representative.hom.app (P, Q))) h
  simp only [Category.assoc, ← Functor.map_comp, Iso.inv_hom_id_app] at hh
  erw [(shiftFunctor (Der R) n).map_id, Category.comp_id] at hh
  convert (show _ from hh.symm) using 1 <;>
    simp only [NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app,
      representativeSecond, NatIso.ofComponents_hom_app,
      Functor.commShiftIso_comp_hom_app, Functor.commShiftIso_map₂CochainComplex_hom_app,
      Functor.comp_obj, inclusionShift,
      Functor.curry_obj_obj_map, Iso.app_hom,
      Category.assoc]
  all_goals (erw [CategoryTheory.Functor.map_id, Category.id_comp]; rfl)

private theorem resolvingExact (a : TensorModel R) [sa : TensorShifts a]
    (P : CochainComplex (Mod R) ℤ) (hp : resolving R P) :
    ((Functor.curry.obj a.functor).obj (DerivedCategory.Q.obj P)).IsTriangulated := by
  let := sa.tensorAdditive
  let := sa.tensorObjAdditive
  let := resolvingStable a
  let := resolvingEssSurj (R := R)
  obtain ⟨e, he⟩ := ringedProjectionTensorModelIso a
  obtain ⟨s, hs⟩ := SheafOfModules.KFlatFixedTensor.kFlat_fixed_tensor_triangulated R
  let := s
  have hf := hs P hp.1 hp.2
  have := hf.2.2.1.1
  obtain ⟨c, hc, hn⟩ := hf.2.2.2.1
  let := hc
  let q := (resolving R).ι ⋙ DerivedCategory.Q
  let eP : (SheafOfModules.KFlatFixedTensor.derivedTensor R).obj
      (DerivedCategory.Q.obj P) ≅
      (Functor.curry.obj a.functor).obj (DerivedCategory.Q.obj P) :=
    (Functor.curry.mapIso e).app (DerivedCategory.Q.obj P)
  let cP := Functor.isoWhiskerLeft (resolving R).ι c ≪≫
    (Functor.associator (resolving R).ι DerivedCategory.Q
      ((SheafOfModules.KFlatFixedTensor.derivedTensor R).obj
        (DerivedCategory.Q.obj P))).symm
  let rP := representativeSecond a ⟨P, hp⟩
  have hr : NatTrans.CommShift rP.hom ℤ := representativeSecondShift a ⟨P, hp⟩
  have hcomp : Functor.whiskerLeft q eP.hom = cP.inv ≫ rP.hom := by
    apply (cancel_epi cP.hom).1
    simp only [← Category.assoc, Iso.hom_inv_id, Category.id_comp]
    ext Q
    simp only [cP, Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app,
      Functor.associator_inv_app, Category.comp_id]
    change c.hom.app Q.obj ≫ e.hom.app
      (DerivedCategory.Q.obj P, DerivedCategory.Q.obj Q.obj) =
        a.representative.hom.app (⟨P, hp⟩, Q)
    rw [show c.hom.app Q.obj =
      (SheafOfModules.KFlatFixedTensor.representativeIso R P Q.obj
        hp.1 Q.property.1 hp.2 Q.property.2).hom from
      congrArg Iso.hom (hn Q.obj Q.property.1 Q.property.2)]
    exact he P Q.obj hp Q.property
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

/-- Fixed-factor tensor is exact for the specified normalized integer shifts. -/
theorem ringedProjectionTensorExact
    {C : Type (u + 1)} [Category.{u} C] [EssentiallySmall.{u + 1} C]
    {J : GrothendieckTopology C} {R : Sheaf J CommRingCat.{u + 1}}
    (a : TensorModel R) [sa : TensorShifts a] (E : Der R) :
    ((Functor.curry.obj a.functor).obj E).IsTriangulated := by
  obtain ⟨P, f, hp, hf⟩ := flatResolution (DerivedCategory.Q.objPreimage E)
  let := hf
  let z : DerivedCategory.Q.obj P ≅ E := asIso (DerivedCategory.Q.map f) ≪≫
    DerivedCategory.Q.objObjPreimageIso E
  have := resolvingExact a P hp
  have : NatTrans.CommShift ((Functor.curry.obj a.functor).mapIso z).hom ℤ :=
    sa.shifts.commShift_map z.hom
  exact Functor.isTriangulated_of_iso ((Functor.curry.obj a.functor).mapIso z)

end AlgebraicGeometry.Scheme.ProjectionRestriction
