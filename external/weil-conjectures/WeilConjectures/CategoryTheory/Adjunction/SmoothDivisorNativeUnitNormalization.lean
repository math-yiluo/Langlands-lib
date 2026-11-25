/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.CategoryTheory.Derived.DerivedAdjunctionCochainUnit
public import WeilConjectures.CategoryTheory.RightDerivedSingleZeroUnit
import all Mathlib.Algebra.Homology.Localization

/-! # Degree zero of the derived adjunction unit on a single object

Source: the formal support-triangle step of native smooth-divisor bottom descent.
(blueprint: lem-pur-derived-unit-single-bottom).
-/

@[expose] public noncomputable section
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory.Adjunction

private theorem rightDerivedUnitQ_single_zero
    {C E : Type*} [Category C] [Category E] [Abelian C] [Abelian E]
    [HasDerivedCategory C] [HasDerivedCategory E]
    [EnoughInjectives C] [Abelian.HasKInjectiveResolutions C]
    (F : C ⥤ E) [F.Additive] [PreservesFiniteLimits F] (M : C) :
    IsIso ((DerivedCategory.homologyFunctor E 0).map
      (F.rightDerivedFunctorUnitQ ((CochainComplex.singleFunctor C 0).obj M))) := by
  let H := DerivedCategory.homologyFunctor E 0
  let e := F.homologyRightDerivedFunctorObjSingleFunctorIso M 0 ≪≫
    F.rightDerivedZeroIsoSelf.app M
  have he := F.rightDerivedSingleUnit_zero M
  have hsingle : IsIso (H.map (F.rightDerivedSingleUnit M) ≫ e.hom) := by
    rw [he]
    infer_instance
  let : IsIso (H.map (F.rightDerivedSingleUnit M)) :=
    IsIso.of_isIso_comp_right _ e.hom
  let t := (F.mapCochainComplexSingleFunctor 0).app M
  have hq : F.rightDerivedSingleUnit M = DerivedCategory.Q.map t.inv ≫
      F.rightDerivedFunctorUnitQ ((CochainComplex.singleFunctor C 0).obj M) := by
    dsimp only [Functor.rightDerivedSingleUnit, Functor.rightDerivedFunctorUnitQ, t]
    change _ = _ ≫ (𝟙 _ ≫ _ ≫ F.rightDerivedFunctor.map (𝟙 _))
    rw [F.rightDerivedFunctor.map_id, Category.id_comp, Category.comp_id]
    rfl
  have hcomp : IsIso (H.map (DerivedCategory.Q.map t.inv) ≫ H.map
      (F.rightDerivedFunctorUnitQ ((CochainComplex.singleFunctor C 0).obj M))) := by
    rw [← H.map_comp, ← hq]
    infer_instance
  exact IsIso.of_isIso_comp_left (H.map (DerivedCategory.Q.map t.inv)) _

private theorem rightDerivedUnitQ_zero_of_single_iso
    {C E : Type*} [Category C] [Category E] [Abelian C] [Abelian E]
    [HasDerivedCategory C] [HasDerivedCategory E]
    [EnoughInjectives C] [Abelian.HasKInjectiveResolutions C]
    (F : C ⥤ E) [F.Additive] [PreservesFiniteLimits F]
    (K : CochainComplex C ℤ) (M : C)
    (e : K ≅ (CochainComplex.singleFunctor C 0).obj M) :
    IsIso ((DerivedCategory.homologyFunctor E 0).map (F.rightDerivedFunctorUnitQ K)) := by
  let H := DerivedCategory.homologyFunctor E 0
  let := rightDerivedUnitQ_single_zero F M
  have hn := congrArg H.map (F.rightDerivedFunctorUnitQ_naturality e.hom)
  simp only [H.map_comp] at hn
  have hcomp : IsIso (H.map (F.rightDerivedFunctorUnitQ K) ≫
      H.map (F.rightDerivedFunctor.map (DerivedCategory.Q.map e.hom))) := by
    rw [← hn]
    infer_instance
  exact IsIso.of_isIso_comp_right _
    (H.map (F.rightDerivedFunctor.map (DerivedCategory.Q.map e.hom)))

/-- The canonical derived adjunction unit on a single object is invertible in degree zero
whenever the ordinary adjunction unit is invertible.
Source: Stacks Project, Tags 0DVC and 0156; Step 1 of native smooth-divisor bottom descent.
Proof: degree zero of the right-derived comparison on a single object is invertible,
by its normalization to the zeroth classical derived functor. Naturality transports
this to the image of a single complex under the exact left adjoint. The cochain
normalization of the derived adjunction unit writes it as the ordinary cochain unit
followed by this comparison. The ordinary unit is an isomorphism termwise on the
single complex: in degree zero by hypothesis, and elsewhere because both objects
are zero. Apply degree-zero homology and cancel the exact-functor comparison. Finally
transport from the quotient of the single complex to the canonical single object.
(blueprint: lem-pur-derived-unit-single-bottom). -/
private theorem derived_unit_single_zero_of_unit
    {C E : Type*} [Category C] [Category E] [Abelian C] [Abelian E]
    [HasDerivedCategory C] [HasDerivedCategory E]
    [EnoughInjectives E] [Abelian.HasKInjectiveResolutions E]
    {L : C ⥤ E} {F : E ⥤ C} [L.Additive] [F.Additive]
    [PreservesFiniteLimits L] [PreservesFiniteColimits L]
    (adj : L ⊣ F) (M : C) (hη : IsIso (adj.unit.app M)) :
    IsIso ((DerivedCategory.homologyFunctor C 0).map
      (adj.mapDerivedCategoryRightDerivedAdjunction.unit.app
        ((DerivedCategory.singleFunctor C 0).obj M))) := by
  let : PreservesFiniteLimits F := by
    let := adj.rightAdjoint_preservesLimits
    infer_instance
  let := hη
  let H := DerivedCategory.homologyFunctor C 0
  let K := (CochainComplex.singleFunctor C 0).obj M
  let a := adj.mapDerivedCategoryRightDerivedAdjunction
  let u := (adj.mapHomologicalComplex (.up ℤ)).unit.app K
  have hY (Y : C) (e : Y ≅ M) : IsIso (adj.unit.app Y) := by
    have hn := adj.unit.naturality e.hom
    simp only [Functor.id_map, Functor.comp_map] at hn
    have : IsIso (adj.unit.app Y ≫ F.map (L.map e.hom)) := by
      rw [← hn]
      infer_instance
    exact IsIso.of_isIso_comp_right _ (F.map (L.map e.hom))
  have (n : ℤ) : IsIso (u.f n) := by
    by_cases hn : n = 0
    · subst hn
      exact hY _ (HomologicalComplex.singleObjXSelf _ 0 M)
    · have hz := HomologicalComplex.isZero_single_obj_X (.up ℤ) 0 M n hn
      exact ⟨⟨0, hz.eq_of_src _ _, (F.map_isZero (L.map_isZero hz)).eq_of_src _ _⟩⟩
  let : IsIso u := HomologicalComplex.Hom.isIso_of_components u
  let := rightDerivedUnitQ_zero_of_single_iso F
    ((L.mapHomologicalComplex (.up ℤ)).obj K) (L.obj M)
    ((L.mapCochainComplexSingleFunctor 0).app M)
  have hn := congrArg H.map (derived_unit_cochain adj K)
  simp only [H.map_comp] at hn
  have hcomp : IsIso (H.map (a.unit.app (DerivedCategory.Q.obj K)) ≫
      H.map (F.rightDerivedFunctor.map (L.mapDerivedCategoryFactors.hom.app K))) := by
    rw [hn]
    infer_instance
  let hu : IsIso (H.map (a.unit.app (DerivedCategory.Q.obj K))) :=
    IsIso.of_isIso_comp_right _
      (H.map (F.rightDerivedFunctor.map (L.mapDerivedCategoryFactors.hom.app K)))
  let e := (DerivedCategory.singleFunctorIsoCompQ C 0).app M
  have he := congrArg H.map (a.unit.naturality e.hom)
  simp only [Functor.id_map, H.map_comp] at he
  have hunit : IsIso (H.map (a.unit.app ((DerivedCategory.singleFunctor C 0).obj M)) ≫
      H.map ((L.mapDerivedCategory ⋙ F.rightDerivedFunctor).map e.hom)) := by
    rw [← he]
    exact IsIso.comp_isIso' (inferInstanceAs (IsIso (H.map e.hom))) hu
  exact IsIso.of_isIso_comp_right _
    (H.map ((L.mapDerivedCategory ⋙ F.rightDerivedFunctor).map e.hom))


/-- Invertibility of the ordinary adjunction unit is equivalent to invertibility
of degree zero of the canonical derived unit on a single object.
Source: Stacks Project, Tags 0DVC and 0156; native bottom descent Step 1.
Proof: the cochain normalization factors the derived unit through the ordinary
cochain unit and the right-derived comparison. The latter is invertible in degree
zero on a single object. Exactness of the left adjoint identifies its image with
a single complex. The additive right adjoint also commutes with single complexes.
Under these comparisons the ordinary cochain unit is the single complex of the
ordinary unit, by naturality. Degree-zero homology of the single functor is the
identity, so all the comparison factors can be cancelled in both directions.
(blueprint: lem-pur-derived-unit-single-bottom). -/
theorem derived_unit_single_zero_isIso_iff
    {C E : Type*} [Category C] [Category E] [Abelian C] [Abelian E]
    [HasDerivedCategory C] [HasDerivedCategory E]
    [EnoughInjectives E] [Abelian.HasKInjectiveResolutions E]
    {L : C ⥤ E} {F : E ⥤ C} [L.Additive] [F.Additive]
    [PreservesFiniteLimits L] [PreservesFiniteColimits L]
    (adj : L ⊣ F) (M : C) :
    IsIso ((DerivedCategory.homologyFunctor C 0).map
      (adj.mapDerivedCategoryRightDerivedAdjunction.unit.app
        ((DerivedCategory.singleFunctor C 0).obj M))) ↔ IsIso (adj.unit.app M) := by
  constructor
  · intro hη
    let : PreservesFiniteLimits F := by
      let := adj.rightAdjoint_preservesLimits
      infer_instance
    let := hη
    let H := DerivedCategory.homologyFunctor C 0
    let K := (CochainComplex.singleFunctor C 0).obj M
    let a := adj.mapDerivedCategoryRightDerivedAdjunction
    let u := (adj.mapHomologicalComplex (.up ℤ)).unit.app K
    let e := (DerivedCategory.singleFunctorIsoCompQ C 0).app M
    have he := congrArg H.map (a.unit.naturality e.hom)
    simp only [Functor.id_map, H.map_comp] at he
    change H.map e.hom ≫ H.map (a.unit.app (DerivedCategory.Q.obj K)) = _ at he
    have hQcomp : IsIso (H.map e.hom ≫ H.map (a.unit.app (DerivedCategory.Q.obj K))) := by
      rw [he]
      infer_instance
    let : IsIso (H.map (a.unit.app (DerivedCategory.Q.obj K))) :=
      IsIso.of_isIso_comp_left (H.map e.hom) _
    let := rightDerivedUnitQ_zero_of_single_iso F
      ((L.mapHomologicalComplex (.up ℤ)).obj K) (L.obj M)
      ((L.mapCochainComplexSingleFunctor 0).app M)
    have hn := congrArg H.map (derived_unit_cochain adj K)
    simp only [H.map_comp] at hn
    have hucomp : IsIso (H.map (DerivedCategory.Q.map u) ≫
        H.map (F.rightDerivedFunctorUnitQ
          ((L.mapHomologicalComplex (.up ℤ)).obj K))) := by
      rw [← hn]
      infer_instance
    let : IsIso (H.map (DerivedCategory.Q.map u)) :=
      IsIso.of_isIso_comp_right _ (H.map (F.rightDerivedFunctorUnitQ
        ((L.mapHomologicalComplex (.up ℤ)).obj K)))
    let tL := (HomologicalComplex.singleMapHomologicalComplex L (.up ℤ) 0).app M
    let tF := (HomologicalComplex.singleMapHomologicalComplex F (.up ℤ) 0).app (L.obj M)
    let t := (F.mapHomologicalComplex (.up ℤ)).mapIso tL ≪≫ tF
    have hv : u ≫ t.hom = (CochainComplex.singleFunctor C 0).map (adj.unit.app M) := by
      ext n
      by_cases hn : n = 0
      · subst n
        change adj.unit.app
          (((HomologicalComplex.single C (.up ℤ) 0).obj M).X 0) ≫
            F.map (((HomologicalComplex.singleMapHomologicalComplex L (.up ℤ) 0).hom.app
              M).f 0) ≫
            ((HomologicalComplex.singleMapHomologicalComplex F (.up ℤ) 0).hom.app
              (L.obj M)).f 0 =
          ((HomologicalComplex.single C (.up ℤ) 0).map (adj.unit.app M)).f 0
        rw [HomologicalComplex.singleMapHomologicalComplex_hom_app_self,
          HomologicalComplex.singleMapHomologicalComplex_hom_app_self,
          HomologicalComplex.single_map_f_self]
        have hn := adj.unit.naturality (HomologicalComplex.singleObjXSelf (.up ℤ) 0 M).hom
        simp only [Functor.id_map, Functor.comp_map] at hn
        simpa only [Functor.comp_obj, Functor.id_obj, Functor.map_comp, Category.assoc,
          Iso.inv_hom_id_assoc, ← Functor.map_comp_assoc,
          Iso.inv_hom_id, Functor.map_id, Category.id_comp, Category.comp_id] using
          congrArg (fun f ↦ f ≫
            (HomologicalComplex.singleObjXSelf (.up ℤ) 0 (F.obj (L.obj M))).inv) hn.symm
      · exact (HomologicalComplex.isZero_single_obj_X (.up ℤ) 0 M n hn).eq_of_src _ _
    have hs : IsIso ((DerivedCategory.homologyFunctor C 0).map
        ((DerivedCategory.singleFunctor C 0).map (adj.unit.app M))) := by
      change IsIso (H.map (DerivedCategory.Q.map
        ((CochainComplex.singleFunctor C 0).map (adj.unit.app M))))
      rw [← hv, DerivedCategory.Q.map_comp, H.map_comp]
      infer_instance
    exact (NatIso.isIso_map_iff
      (DerivedCategory.singleFunctorCompHomologyFunctorIso C 0) (adj.unit.app M)).mp hs
  · exact derived_unit_single_zero_of_unit adj M


end CategoryTheory.Adjunction
