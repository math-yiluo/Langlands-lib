/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.DerivedTensorStructure
public import WeilConjectures.AlgebraicGeometry.DerivedPullback
public import WeilConjectures.AlgebraicGeometry.SchemeDerivedDirectImage
import Mathlib.CategoryTheory.Adjunction.Mates
import WeilConjectures.AlgebraicGeometry.DerivedPullbackStructureSheaf
import WeilConjectures.CategoryTheory.DerivedCategory.FlatModel

/-! # Projection mates on shifted structure sheaves

Source: Stacks Project, Tag 08EU, final sentence of the proof.
(blueprint: lem-pc-qcqs-projection-mate-shifted-unit).
-/

@[expose] public section

universe u w
open CategoryTheory MonoidalCategory
namespace AlgebraicGeometry

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem equivalence_projection_mate_isIso
    {C D : Type*} [Category C] [Category D]
    {F : C ⥤ D} {G : D ⥤ C} (p : F ⊣ G)
    (A : C ≌ C) (B : D ≌ D) (α : A.functor ⋙ F ≅ F ⋙ B.functor) (L : D) :
    IsIso (p.homEquiv (A.functor.obj (G.obj L)) (B.functor.obj L)
      (α.hom.app (G.obj L) ≫ B.functor.map (p.counit.app L))) := by
  let a := A.symm.toAdjunction
  let b := B.symm.toAdjunction
  let β := (mateEquiv a b).symm (TwoSquare.mk _ _ _ _ α.hom)
  have hβ : IsIso β := by
    dsimp [β, mateEquiv]
    infer_instance
  let γ := conjugateEquiv (a.comp p) (p.comp b) β
  have hγ : IsIso γ := conjugateEquiv_iso _ _ _
  have heq : γ.app L = p.homEquiv (A.functor.obj (G.obj L)) (B.functor.obj L)
      (α.hom.app (G.obj L) ≫ B.functor.map (p.counit.app L)) := by
    simp only [Equivalence.symm_inverse, Functor.comp_obj, Equivalence.symm_functor,
      conjugateEquiv, Iso.homCongr_symm, Equiv.trans_def, mateEquiv, mateEquiv_symm_apply,
      Equivalence.toAdjunction_unit, Equivalence.symm_unit, Equivalence.toAdjunction_counit,
      Equivalence.symm_counit, Equiv.trans_apply, Iso.homCongr_apply, Iso.symm_inv, Iso.symm_hom,
      Category.assoc, Iso.hom_inv_id, Category.comp_id, Iso.hom_inv_id_assoc,
      Equiv.coe_fn_mk, Functor.whiskerRight_comp,
      Functor.whiskerRight_twice, Iso.inv_hom_id_assoc, Functor.whiskerLeft_comp,
      NatTrans.comp_app, Functor.id_obj,
      Functor.rightUnitor_inv_app, Functor.whiskerLeft_app, Adjunction.comp_unit_app,
      Functor.associator_hom_app, Functor.associator_inv_app, Functor.whiskerRight_app,
      Functor.comp_map, Equivalence.fun_inv_map, Functor.map_comp, CategoryTheory.Functor.map_id,
      Adjunction.comp_counit_app, Functor.id_map, Functor.leftUnitor_hom_app, Category.id_comp,
      cancelIso, Adjunction.unit_naturality_assoc, Adjunction.homEquiv_unit, γ, b, a, β]
    change A.counitInv.app (A.functor.obj (G.obj L)) ≫
      p.unit.app (A.functor.obj (A.inverse.obj (A.functor.obj (G.obj L)))) ≫
      G.map (α.hom.app (A.inverse.obj (A.functor.obj (G.obj L)))) ≫
      G.map (B.counitInv.app (B.functor.obj
        (F.obj (A.inverse.obj (A.functor.obj (G.obj L)))))) ≫
      G.map (B.functor.map (B.unitInv.app
        (F.obj (A.inverse.obj (A.functor.obj (G.obj L)))))) ≫
      G.map (B.functor.map (F.map (A.unitInv.app (G.obj L)))) ≫
      G.map (B.functor.map (p.counit.app L)) = _
    have hb (Z : D) : B.counitInv.app (B.functor.obj Z) ≫
        B.functor.map (B.unitInv.app Z) = 𝟙 _ := B.counitInv_functor_comp Z
    slice_lhs 4 5 =>
      rw [← G.map_comp, hb]
      dsimp only [Functor.comp_obj, Functor.id_obj]
      rw [G.map_id]
    dsimp only [Functor.comp_obj, Functor.id_obj]
    simp only [Category.id_comp]
    have hp {U V : C} (h : U ⟶ V) :
        h ≫ p.unit.app V = p.unit.app U ≫ G.map (F.map h) := p.unit.naturality h
    rw [← Category.assoc]
    erw [hp]
    rw [Category.assoc]
    have ht := α.hom.naturality (A.unitInv.app (G.obj L))
    change F.map (A.functor.map (A.unitInv.app (G.obj L))) ≫ α.hom.app (G.obj L) =
      α.hom.app (A.inverse.obj (A.functor.obj (G.obj L))) ≫
        B.functor.map (F.map (A.unitInv.app (G.obj L))) at ht
    slice_lhs 3 4 => rw [← G.map_comp, ← ht, G.map_comp]
    slice_lhs 2 3 =>
      rw [← G.map_comp, ← F.map_comp, A.counitInv_functor_comp, F.map_id, G.map_id]
    dsimp only [Functor.comp_obj, Functor.id_obj]
    simp only [Category.id_comp]
  rw [← heq]
  infer_instance

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem shifted_unit_tensorLeft_isEquivalence (X : Scheme.{u})
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings X.toRingedSpace))]
    (k : ℤ) :
    (tensorLeft (((DerivedCategory.singleFunctor
      (SheafOfModules.{u} (moduleRings X.toRingedSpace)) 0).obj
      (SheafOfModules.unit (moduleRings X.toRingedSpace)))⟦k⟧)).IsEquivalence := by
  let A := SheafOfModules.{u} (moduleRings X.toRingedSpace)
  let : Category.{u} A := inferInstance
  let : CategoryTheory.Abelian A := inferInstance
  let : MonoidalCategory A := SheafOfModules.monoidalCategory X.sheaf
  let := SheafOfModules.symmetricCategory X.sheaf
  have : MonoidalPreadditive A := Classical.choice (SheafOfModules.tensorClosed X.sheaf).1
  let : MonoidalClosed A := Classical.choice (SheafOfModules.tensorClosed X.sheaf).2.1
  have : CategoryTheory.IsGrothendieckAbelian.{u} A :=
    SheafOfModules.isGrothendieckAbelian (moduleRings X.toRingedSpace)
  have : CategoryTheory.Limits.HasColimitsOfSize.{0, 0} A :=
    CategoryTheory.Limits.hasColimitsOfSizeShrink.{0, 0, u, u} A
  have := schemeModule_hasFunctorialFlatResolution X
  have (P Q : GradedObject ℤ A) : P.HasTensor Q := by
    dsimp only [GradedObject.HasTensor]
    infer_instance
  have (Z : A) : CategoryTheory.Limits.PreservesColimitsOfShape ℤ (tensorRight Z) :=
    CategoryTheory.Limits.preservesColimitsOfShape_of_natIso
      (F := tensorLeft Z) (BraidedCategory.tensorLeftIsoTensorRight Z)
  have : CategoryTheory.HasExactColimitsOfShape ℤ A := inferInstance
  have (Z : A) : CategoryTheory.Limits.PreservesColimitsOfShape ℤ
      ((curriedTensor A).obj Z) := inferInstance
  have (j : ℤ) : CategoryTheory.Limits.HasColimitsOfShape
      (Discrete ((ComplexShape.up ℤ).π (ComplexShape.up ℤ) (ComplexShape.up ℤ) ⁻¹' {j})) A :=
    inferInstance
  have (P Q R S : GradedObject ℤ A) : GradedObject.HasTensor₄ObjExt P Q R S :=
    inferInstance
  have (P Q R : GradedObject ℤ A) : GradedObject.HasGoodTensor₁₂Tensor P Q R :=
    inferInstance
  have (P Q R : GradedObject ℤ A) : GradedObject.HasGoodTensorTensor₂₃ P Q R :=
    inferInstance
  have (Z : A) : CategoryTheory.Limits.PreservesColimit (Functor.empty.{0} A)
      ((curriedTensor A).obj Z) := inferInstance
  have (Z : A) : CategoryTheory.Limits.PreservesColimit (Functor.empty.{0} A)
      ((curriedTensor A).flip.obj Z) :=
    CategoryTheory.Limits.preservesColimit_of_natIso _
      (BraidedCategory.tensorLeftIsoTensorRight Z)
  let W := HomotopyCategory.quasiIso A (ComplexShape.up ℤ)
  have : W.localizerMorphismKFlat.IsLeftDerivabilityStructure := inferInstance
  let U := (DerivedCategory.singleFunctor A 0).obj (𝟙_ A)
  let eU := DerivedCategory.singleFunctorObjUnitIso.{w, u, u + 1} A
  let H := HomotopyCategory A (ComplexShape.up ℤ)
  let : MonoidalCategory H := inferInstance
  let q := HomotopyCategory.quotient A (ComplexShape.up ℤ)
  let V := (CochainComplex.singleFunctor A 0).obj (𝟙_ A)
  let eV : U ≅ DerivedCategory.Qh.obj (𝟙_ H) :=
    (DerivedCategory.singleFunctorIsoCompQ A 0).app (𝟙_ A) ≪≫
      ((DerivedCategory.quotientCompQhIso A).app V).symm ≪≫
      DerivedCategory.Qh.mapIso (Functor.Monoidal.εIso q).symm
  let e (a b : ℤ) (h : a + b = 0) : U⟦a⟧ ⊗ U⟦b⟧ ≅ 𝟙_ (schemeDerivedCategory X) := by
    let P : H := (𝟙_ H)⟦b⟧
    have hP : W.kFlat P := W.kFlat.le_shift b _ (ObjectProperty.prop_unit W.kFlat)
    let eP : DerivedCategory.Qh.obj P ≅ U⟦b⟧ :=
      ((DerivedCategory.Qh (C := A)).commShiftIso b).app (𝟙_ H) ≪≫
        (shiftFunctor _ b).mapIso eV.symm
    let := DerivedCategory.commShiftTensorRightQhObj P hP
    let := Functor.CommShift.ofIso ((curriedTensor _).flip.mapIso eP) ℤ
    exact ((tensorRight (U⟦b⟧)).commShiftIso a).app U ≪≫
      (shiftFunctor _ a).mapIso (whiskerRightIso eU (U⟦b⟧) ≪≫ λ_ _) ≪≫
      (shiftFunctorAdd' (schemeDerivedCategory X) b a 0 (by omega)).symm.app U ≪≫
      (shiftFunctorZero (schemeDerivedCategory X) ℤ).app U ≪≫ eU
  let E : schemeDerivedCategory X ≌ schemeDerivedCategory X :=
    .mk (tensorLeft (U⟦k⟧)) (tensorLeft (U⟦-k⟧))
      ((leftUnitorNatIso _).symm ≪≫ (curriedTensor _).mapIso (e (-k) k (by omega)).symm ≪≫
        tensorLeftTensor _ _)
      ((tensorLeftTensor _ _).symm ≪≫ (curriedTensor _).mapIso (e k (-k) (by omega)) ≪≫
        leftUnitorNatIso _)
  exact E.isEquivalence_functor

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The supplied projection mate is invertible when the first factor is a shifted
structure sheaf. No quasi-compactness or quasi-coherence hypothesis is needed.
Source: Stacks Project, Tag 08EU, final sentence of the proof.
(blueprint: lem-pc-qcqs-projection-mate-shifted-unit).

Proof: derived pullback takes the structure sheaf to the structure sheaf and
commutes with shifts. Tensoring with O[k] identifies naturally with translation
by k. These identifications turn t(O[k],-) into a natural isomorphism between
the two shifted versions of pullback. The adjunction between pullback and direct
image induces an adjunction between their shifted versions; the canonical
pullback shift isomorphism induces the direct-image shift isomorphism by mates.
Under these isomorphisms the displayed projection mate is the adjunction
conjugate of the supplied comparison at O[k]. Conjugation preserves inverses,
as follows by inserting the unit/counit formulas and cancelling the two triangle
identities. Thus it is an isomorphism, for any p and t. Naturality in M,
obtained from naturality of t and the counit and the Hom equivalence, transports
the result along hM. For k = 0 this is the unit triangle calculation, modified
by an arbitrary natural automorphism of pullback and its conjugate; for empty
schemes every map here is the unique isomorphism of zero objects. -/
theorem qcqsProjectionMate_shiftedUnit_isIso (X Y : Scheme.{u})
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings X.toRingedSpace))]
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))]
    (f : X ⟶ Y) (p : derivedPullback f ⊣ schemeDerivedDirectImage f)
    (t : tensor (schemeDerivedCategory Y) ⋙ derivedPullback f ≅
      (derivedPullback f).prod (derivedPullback f) ⋙ tensor (schemeDerivedCategory X))
    (M : schemeDerivedCategory Y) (L : schemeDerivedCategory X) (k : ℤ)
    (hM : Nonempty (M ≅
      ((DerivedCategory.singleFunctor
        (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) 0).obj
        (SheafOfModules.unit (moduleRings Y.toRingedSpace)))⟦k⟧)) :
    IsIso (p.homEquiv (M ⊗ (schemeDerivedDirectImage f).obj L)
      ((derivedPullback f).obj M ⊗ L)
        (t.hom.app (M, (schemeDerivedDirectImage f).obj L) ≫
          (𝟙 ((derivedPullback f).obj M) ⊗ₘ p.counit.app L))) := by
  classical
  obtain ⟨eM⟩ := hM
  have := shifted_unit_tensorLeft_isEquivalence Y k
  have hAM : (tensorLeft M).IsEquivalence :=
    Functor.isEquivalence_of_iso ((curriedTensor _).mapIso eM).symm
  obtain ⟨I, hI, hImap, hIadd, hIlim, hIcolim, hIres,
    E, hE, hEmap, hEadd, ε, hε, ⟨s, htri⟩, hεflat⟩ :=
    (derivedPullback_spec f)
  let : (derivedPullback f).CommShift ℤ := s
  obtain ⟨eU⟩ := nonempty_derivedPullback_structureSheaf_iso f
  let UY := (DerivedCategory.singleFunctor
    (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) 0).obj
      (SheafOfModules.unit (moduleRings Y.toRingedSpace))
  let eFM := (derivedPullback f).mapIso eM ≪≫
    ((derivedPullback f).commShiftIso k).app UY ≪≫ (shiftFunctor _ k).mapIso eU
  have := shifted_unit_tensorLeft_isEquivalence X k
  have hBFM : (tensorLeft ((derivedPullback f).obj M)).IsEquivalence :=
    Functor.isEquivalence_of_iso ((curriedTensor _).mapIso eFM).symm
  let α : tensorLeft M ⋙ derivedPullback f ≅
      derivedPullback f ⋙ tensorLeft ((derivedPullback f).obj M) :=
    NatIso.ofComponents (fun N ↦ t.app (M, N)) (by
      intro N N' a
      have h := t.hom.naturality ((𝟙 M, a) : (M, N) ⟶ (M, N'))
      simpa using h)
  have h := equivalence_projection_mate_isIso p
    (tensorLeft M).asEquivalence (tensorLeft ((derivedPullback f).obj M)).asEquivalence α L
  erw [CategoryTheory.MonoidalCategory.id_tensorHom]
  simpa only [Functor.prod_obj, Functor.comp_obj, Functor.asEquivalence, α,
    NatIso.ofComponents, tensorLeft, curriedTensor,
    Iso.app_hom, CategoryTheory.MonoidalCategory.id_tensorHom] using h

end AlgebraicGeometry
