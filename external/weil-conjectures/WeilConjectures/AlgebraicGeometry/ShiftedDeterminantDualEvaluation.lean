/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.DerivedTensorStructure
public import WeilConjectures.AlgebraicGeometry.Modules.ExteriorPower
public import WeilConjectures.AlgebraicGeometry.Modules.LocallyFreeRank
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.InternalHom
import WeilConjectures.AlgebraicGeometry.DeterminantDualEvaluation
import WeilConjectures.CategoryTheory.Abelian.Flat.Basic
import WeilConjectures.CategoryTheory.DerivedCategory.Monoidal.Unit

/-! # The shifted determinant of the dual evaluates against the determinant

Source: Stacks Project, Tag 0BRT, determinant inversion in the conclusion of the proof.
(blueprint: lem-sc-shifted-determinant-dual-evaluation).
-/

@[expose] public section

universe u w

open CategoryTheory MonoidalCategory

namespace AlgebraicGeometry

/-- The degree-zero single object as the localization of its single complex.
This is the general form of the comparison in Etale.Derived.Invertible. -/
private noncomputable def singleObjIsoQh
    {C : Type*} [Category C] [Abelian C] [IsGrothendieckAbelian.{u} C]
    [HasDerivedCategory.{w} C] [MonoidalCategory C] [MonoidalPreadditive C]
    [BraidedCategory C] [MonoidalClosed C] [Abelian.HasFunctorialFlatResolution C]
    [CategoryTheory.Limits.HasColimitsOfSize.{0, 0} C] (F : C) :
    (DerivedCategory.singleFunctor C 0).obj F ≅
      DerivedCategory.Qh.obj ((HomotopyCategory.quotient C (.up ℤ)).obj
        ((HomologicalComplex.single C (.up ℤ) 0).obj F)) :=
  (DerivedCategory.singleFunctorIsoCompQ C 0).app F ≪≫
    (DerivedCategory.quotientCompQhIso C).symm.app _

/-- The derived unit is the single object of the ordinary unit, using the invertible
unit comparison of Qh. -/
private noncomputable def singleObjUnitIso
    {C : Type*} [Category C] [Abelian C] [IsGrothendieckAbelian.{u} C]
    [HasDerivedCategory.{w} C] [MonoidalCategory C] [MonoidalPreadditive C]
    [BraidedCategory C] [MonoidalClosed C] [Abelian.HasFunctorialFlatResolution C]
    [CategoryTheory.Limits.HasColimitsOfSize.{0, 0} C] :
    (DerivedCategory.singleFunctor C 0).obj (𝟙_ C) ≅ 𝟙_ (DerivedCategory C) :=
  have := DerivedCategory.isIso_ε_Qh C
  singleObjIsoQh (𝟙_ C) ≪≫
    DerivedCategory.Qh.mapIso
      ((Functor.Monoidal.εIso (HomotopyCategory.quotient C (.up ℤ))).symm :
        (HomotopyCategory.quotient C (.up ℤ)).obj (𝟙_ (CochainComplex C ℤ)) ≅ _) ≪≫
    (asIso (Functor.LaxMonoidal.ε DerivedCategory.Qh)).symm

/-- A flat single complex is K-flat, so the localization tensor comparison is invertible.
The final two comparisons identify the tensor of single complexes with a single tensor. -/
private noncomputable def singleObjTensorIso
    {C : Type*} [Category C] [Abelian C] [IsGrothendieckAbelian.{u} C]
    [HasDerivedCategory.{w} C] [MonoidalCategory C] [MonoidalPreadditive C]
    [BraidedCategory C] [MonoidalClosed C] [Abelian.HasFunctorialFlatResolution C]
    [CategoryTheory.Limits.HasColimitsOfSize.{0, 0} C] (L F : C) (hL : ObjectProperty.flat L) :
    (DerivedCategory.singleFunctor C 0).obj L ⊗
        (DerivedCategory.singleFunctor C 0).obj F ≅
      (DerivedCategory.singleFunctor C 0).obj (L ⊗ F) := by
  have hK : (HomotopyCategory.quasiIso C (.up ℤ)).kFlat
      ((HomotopyCategory.quotient C (.up ℤ)).obj
        ((HomologicalComplex.single C (.up ℤ) 0).obj L)) :=
    (HomotopyCategory.kFlat_quotient_obj_iff _).2
      ((CochainComplex.kFlat_single_obj_iff_flat L 0).2 hL)
  have : IsIso (((Functor.LaxMonoidal.μNatTrans (DerivedCategory.Qh (C := C))).app
      ((HomotopyCategory.quotient C (.up ℤ)).obj
        ((HomologicalComplex.single C (.up ℤ) 0).obj L))).app
      ((HomotopyCategory.quotient C (.up ℤ)).obj
        ((HomologicalComplex.single C (.up ℤ) 0).obj F))) :=
    DerivedMonoidal.isIso_counit_app_app_of_kFlat_left
      DerivedCategory.Qh (HomotopyCategory.quasiIso C (.up ℤ)) _
      ((HomotopyCategory.quotient C (.up ℤ)).obj
        ((HomologicalComplex.single C (.up ℤ) 0).obj F)) hK
  exact tensorIso (singleObjIsoQh L) (singleObjIsoQh F) ≪≫
    asIso (((Functor.LaxMonoidal.μNatTrans (DerivedCategory.Qh (C := C))).app
      ((HomotopyCategory.quotient C (.up ℤ)).obj
        ((HomologicalComplex.single C (.up ℤ) 0).obj L))).app
      ((HomotopyCategory.quotient C (.up ℤ)).obj
        ((HomologicalComplex.single C (.up ℤ) 0).obj F))) ≪≫
    DerivedCategory.Qh.mapIso
      (Functor.Monoidal.μIso (HomotopyCategory.quotient C (.up ℤ)) _ _) ≪≫
    DerivedCategory.Qh.mapIso ((HomotopyCategory.quotient C (.up ℤ)).mapIso
      (((CochainComplex.map₂HomologicalComplexObjSingleIso (curriedTensor C) L).app _) ≪≫
        ((HomologicalComplex.singleMapHomologicalComplex (tensorLeft L) (.up ℤ) 0).app F))) ≪≫
    (singleObjIsoQh (L ⊗ F)).symm

/-- Transport shift commutation from K-flat representatives in each variable.
Unlike shiftTensorShiftIso, this allows independent Grothendieck and derived universes. -/
private noncomputable def tensorShiftIso
    {C : Type*} [Category C] [Abelian C] [IsGrothendieckAbelian.{u} C]
    [HasDerivedCategory.{w} C] [MonoidalCategory C] [MonoidalPreadditive C]
    [BraidedCategory C] [MonoidalClosed C] [Abelian.HasFunctorialFlatResolution C]
    [CategoryTheory.Limits.HasColimitsOfSize.{0, 0} C] (A B : DerivedCategory C) (a b : ℤ) :
    A⟦a⟧ ⊗ B⟦b⟧ ≅ (A ⊗ B)⟦a + b⟧ := by
  classical
  let P := Classical.choose (DerivedCategory.exists_kFlat_iso A)
  have hP := (Classical.choose_spec (DerivedCategory.exists_kFlat_iso A)).1
  let eP := Classical.choice (Classical.choose_spec (DerivedCategory.exists_kFlat_iso A)).2
  let Q := Classical.choose (DerivedCategory.exists_kFlat_iso (B⟦b⟧))
  have hQ := (Classical.choose_spec (DerivedCategory.exists_kFlat_iso (B⟦b⟧))).1
  let eQ := Classical.choice (Classical.choose_spec (DerivedCategory.exists_kFlat_iso (B⟦b⟧))).2
  letI := DerivedCategory.commShiftTensorLeftQhObj P hP
  letI := DerivedCategory.commShiftTensorRightQhObj Q hQ
  letI : ((curriedTensor (DerivedCategory C)).obj A).CommShift ℤ :=
    Functor.CommShift.ofIso ((curriedTensor (DerivedCategory C)).mapIso eP) ℤ
  letI : ((curriedTensor (DerivedCategory C)).flip.obj (B⟦b⟧)).CommShift ℤ :=
    Functor.CommShift.ofIso ((curriedTensor (DerivedCategory C)).flip.mapIso eQ) ℤ
  exact (((curriedTensor (DerivedCategory C)).flip.obj (B⟦b⟧)).commShiftIso a).app A ≪≫
    (shiftFunctor _ a).mapIso ((((curriedTensor _).obj A).commShiftIso b).app B) ≪≫
    (shiftFunctorAdd' (DerivedCategory C) b a (a + b) (add_comm b a)).symm.app _

/-- The shifted top exterior powers of a finite locally free sheaf and its dual are
mutually inverse derived tensor objects.
Source: Stacks Project, Tag 0BRT, final determinant inversion.
(blueprint: lem-sc-shifted-determinant-dual-evaluation).

Proof: on an open cover trivializing M as O_X^d, use a basis e₁,...,e_d and its dual.
The determinant evaluation pairs their top wedges to 1 and is therefore an isomorphism
from wedge^d M^dual tensor wedge^d M to O_X on that cover. A basis change multiplies
the two determinant generators by inverse determinants, so this evaluation is
independent of the chosen bases and glues. Sectionwise exterior powers sheafify to
these local determinant lines, and internal Hom restricts to the dual free module.
Both determinant lines are locally free of rank one, hence flat, so their ordinary
product computes their derived tensor product. The single functor in degree zero
therefore carries the evaluation to an isomorphism with the derived unit. Compatibility
of derived tensor with shifts identifies the displayed product with that unshifted
product shifted by -d+d=0. Compose with the zero-shift isomorphism. When d=0 the empty
wedge is the structure sheaf and the evaluation is multiplication; the same argument
works on an empty scheme as well. -/
theorem shiftedDeterminant_dual_evaluation
    (X : Scheme.{u})
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings X.toRingedSpace))]
    (M : X.Modules) (d : ℕ) (hfree : M.IsFiniteLocallyFreeOfRank d) :
    Nonempty ((((DerivedCategory.singleFunctor
      (SheafOfModules.{u} (moduleRings X.toRingedSpace)) 0).obj
        (Scheme.Modules.exteriorPower
          (SheafOfModules.homObj (R := X.sheaf) M
            (SheafOfModules.unit X.ringCatSheaf)) d))⟦-(d : ℤ)⟧ ⊗
      ((DerivedCategory.singleFunctor
        (SheafOfModules.{u} (moduleRings X.toRingedSpace)) 0).obj
          (Scheme.Modules.exteriorPower M d))⟦(d : ℤ)⟧) ≅
      𝟙_ (schemeDerivedCategory X)) := by
  let := SheafOfModules.monoidalCategory X.sheaf
  let := SheafOfModules.symmetricCategory X.sheaf
  have : MonoidalPreadditive (SheafOfModules.{u} (moduleRings X.toRingedSpace)) :=
    Classical.choice (SheafOfModules.tensorClosed X.sheaf).1
  let : MonoidalClosed (SheafOfModules.{u} (moduleRings X.toRingedSpace)) :=
    Classical.choice (SheafOfModules.tensorClosed X.sheaf).2.1
  have : IsGrothendieckAbelian.{u} (SheafOfModules.{u} (moduleRings X.toRingedSpace)) :=
    SheafOfModules.isGrothendieckAbelian (moduleRings X.toRingedSpace)
  have := schemeModule_hasFunctorialFlatResolution X
  have : CategoryTheory.Limits.HasColimitsOfSize.{0, 0}
      (SheafOfModules.{u} (moduleRings X.toRingedSpace)) :=
    CategoryTheory.Limits.hasColimitsOfSizeShrink.{0, 0, u, u} _
  obtain ⟨e⟩ := determinant_dual_evaluation X M d hfree
  let L : SheafOfModules.{u} (moduleRings X.toRingedSpace) := Scheme.Modules.exteriorPower
    (SheafOfModules.homObj (R := X.sheaf) M
      (SheafOfModules.unit X.ringCatSheaf)) d
  let F : SheafOfModules.{u} (moduleRings X.toRingedSpace) := Scheme.Modules.exteriorPower M d
  let S := DerivedCategory.singleFunctor
    (SheafOfModules.{u} (moduleRings X.toRingedSpace)) 0
  have hL : ObjectProperty.flat L := ObjectProperty.flat_of_tensorIso e
  let e₀ : S.obj L ⊗ S.obj F ≅ 𝟙_ (schemeDerivedCategory X) :=
    singleObjTensorIso L F hL ≪≫ S.mapIso e ≪≫ singleObjUnitIso
  refine ⟨tensorShiftIso (S.obj L) (S.obj F)
    (-(d : ℤ)) (d : ℤ) ≪≫ ?_⟩
  simpa only [neg_add_cancel, Functor.id_obj] using
    ((shiftFunctor _ (0 : ℤ)).mapIso e₀ ≪≫
      (shiftFunctorZero (schemeDerivedCategory X) ℤ).app _)

end AlgebraicGeometry
