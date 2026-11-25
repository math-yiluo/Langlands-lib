/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module
public import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.Plus
/-!
# Canonical single-complex shift comparisons

These comparisons isolate the source and unit transport calculations used by
`rightDerivedFunctorPlusUnit_canonical_single_shift`.
-/

@[expose] public section
open CategoryTheory CategoryTheory.Limits
variable {C : Type*} [Category* C] [Abelian C] [HasDerivedCategory C]
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
set_option linter.unusedSectionVars false in
private theorem cochain_comparison (Y : C) (n : ℤ) :
    (HomologicalComplex.homologyFunctor C (.up ℤ) 0).shiftMap
      (((CochainComplex.singleFunctors C).shiftIso (-n) n 0 (by simp)).inv.app Y)
      n 0 (by simp) ≫
        (HomologicalComplex.homologyFunctorSingleIso C (.up ℤ) 0).hom.app Y =
      (HomologicalComplex.homologyFunctorSingleIso C (.up ℤ) n).hom.app Y := by
  dsimp [Functor.shiftMap]
  rw [Category.assoc]
  change HomologicalComplex.homologyMap
    (((CochainComplex.singleFunctors C).shiftIso (-n) n 0 (by simp)).inv.app Y) n ≫
    (CochainComplex.ShiftSequence.shiftIso C (-n) n 0 (by simp)).hom.app
      ((CochainComplex.singleFunctor C 0).obj Y) ≫ _ = _
  rw [CochainComplex.ShiftSequence.shiftIso_hom_app]
  rw [← cancel_epi (((CochainComplex.singleFunctor C n).obj Y).homologyπ n)]
  simp only [HomologicalComplex.homologyπ_naturality_assoc,
    HomologicalComplex.homologyFunctorSingleIso_hom_app]
  erw [ShortComplex.homologyπ_naturality_assoc]
  erw [HomologicalComplex.homologyπ_singleObjHomologySelfIso_hom,
    HomologicalComplex.homologyπ_singleObjHomologySelfIso_hom]
  simp only [HomologicalComplex.singleObjCyclesSelfIso_hom]
  erw [ShortComplex.cyclesMap_i_assoc, HomologicalComplex.cyclesMap_i_assoc]
  simp only [CochainComplex.shiftShortComplexFunctorIso,
    CochainComplex.shiftShortComplexFunctor', CochainComplex.shiftEval,
    HomologicalComplex.singleObjXSelf, HomologicalComplex.singleObjXIsoOfEq,
    CategoryTheory.Functor.comp_obj, CochainComplex.shiftFunctor_obj_X']
  dsimp [HomologicalComplex.XIsoOfEq]
  erw [Category.comp_id, eqToHom_trans]
  · simp

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem derived_comparison (Y : C) (n : ℤ) :
    (DerivedCategory.homologyFunctor C 0).shiftMap
      (((DerivedCategory.singleFunctors C).shiftIso (-n) n 0 (by simp)).inv.app Y)
      n 0 (by simp) ≫
        (DerivedCategory.singleFunctorCompHomologyFunctorIso C 0).hom.app Y =
      (DerivedCategory.singleFunctorCompHomologyFunctorIso C n).hom.app Y := by
  have hσ := congr_app ((DerivedCategory.singleFunctorsPostcompQIso C).hom.comm
    (-n) n 0 (by simp)) Y
  simp only [DerivedCategory.singleFunctorsPostcompQIso_hom_hom] at hσ
  dsimp at hσ
  simp only [CategoryTheory.Functor.map_id, Category.id_comp, Category.comp_id,
    SingleFunctors.postcomp_shiftIso_hom_app] at hσ
  change
    (((DerivedCategory.singleFunctors C).shiftIso (-n) n 0 (by simp)).hom.app Y) =
      (DerivedCategory.Q.commShiftIso (-n)).inv.app
        ((CochainComplex.singleFunctor C 0).obj Y) ≫
      DerivedCategory.Q.map
        (((CochainComplex.singleFunctors C).shiftIso (-n) n 0 (by simp)).hom.app Y)
    at hσ
  have hσ' :
      (((DerivedCategory.singleFunctors C).shiftIso (-n) n 0 (by simp)).inv.app Y) =
      ShiftedHom.map
        (((CochainComplex.singleFunctors C).shiftIso (-n) n 0 (by simp)).inv.app Y)
        DerivedCategory.Q := by
    change _ = DerivedCategory.Q.map
      (((CochainComplex.singleFunctors C).shiftIso (-n) n 0 (by simp)).inv.app Y) ≫
      (DerivedCategory.Q.commShiftIso (-n)).hom.app
        ((CochainComplex.singleFunctor C 0).obj Y)
    rw [← cancel_mono
      (((DerivedCategory.singleFunctors C).shiftIso (-n) n 0 (by simp)).hom.app Y)]
    rw [hσ]
    simp only [Category.assoc, Iso.hom_inv_id_app_assoc,
      ← DerivedCategory.Q.map_comp, Iso.inv_hom_id_app,
      CategoryTheory.Functor.map_id]
    rw [← hσ, Iso.inv_hom_id_app]
    rfl
  rw [hσ', DerivedCategory.shiftMap_homologyFunctor_map_Q _ n 0 (by simp)]
  have hχ (i : ℤ) :
      (DerivedCategory.singleFunctorCompHomologyFunctorIso C i).hom.app Y =
        (DerivedCategory.homologyFunctorFactors C i).hom.app
          ((CochainComplex.singleFunctor C i).obj Y) ≫
        (HomologicalComplex.homologyFunctorSingleIso C (.up ℤ) i).hom.app Y := by
    dsimp only [DerivedCategory.singleFunctorCompHomologyFunctorIso, Iso.trans_hom,
      Functor.isoWhiskerRight_hom, Functor.isoWhiskerLeft_hom,
      NatTrans.comp_app, Functor.whiskerRight_app, Functor.whiskerLeft_app,
      Functor.associator_hom_app, CategoryTheory.Functor.mapIso_hom,
      SingleFunctors.evaluation]
    rw [DerivedCategory.singleFunctorsPostcompQIso_hom_hom]
    dsimp only [NatTrans.id_app]
    change (DerivedCategory.homologyFunctor C i).map (𝟙 _) ≫ 𝟙 _ ≫ _ = _
    simp only [CategoryTheory.Functor.map_id, Category.id_comp]
  rw [hχ, hχ]
  dsimp only [HomotopyCategory.singleFunctors, SingleFunctors.postcomp_functor,
    CategoryTheory.Functor.comp_obj, CochainComplex.singleFunctor]
  simp only [Category.assoc]
  erw [Iso.inv_hom_id_app_assoc]
  rw [cochain_comparison]


set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
set_option linter.auxLemma false in
/-- Single-object homology comparisons commute with shift transport to degree zero.

Source: the single-functor shift and homology shift constructions in Mathlib,
`Algebra/Homology/HomotopyCategory/SingleFunctors.lean` and
`Algebra/Homology/HomotopyCategory/ShiftSequence.lean`.
(blueprint: lem-pc-single-homology-shift-comparison)

Proof: Lift the single-functor shift to the bounded-below derived category through
its fully faithful inclusion. The induced homology shift sequence transports the
result back to the homotopy category and then to cochain complexes, by the quotient
homology comparisons. Naturality cancels these quotient comparisons. In cochain
complexes, homology of the inverse single shift followed by the homology shift is
induced by a morphism of short complexes whose middle component is the identity
on Y. Compose with the epimorphic cycles-to-homology projection: naturality of
homologyπ and cyclesMap_i identifies both sides with iCycles followed by
singleObjXSelf.hom. The outer terms of the short complexes are zero, so the signs
in the shift act only on zero morphisms. Cancelling the homology projection proves
the identity. At n=0, the shift unit comparisons cancel; the same argument also
applies to a zero object. -/
theorem singleFunctor_homology_shift_comparison (Y : C) (n : ℤ) :
    let H₀ := DerivedCategory.Plus.homologyFunctor C 0
    let d := Functor.isoWhiskerRight
      ((DerivedCategory.Plus.singleFunctors C).shiftIso (-n) n 0 (by simp)).symm
      (H₀.shift n) ≪≫
      Functor.isoWhiskerLeft (DerivedCategory.Plus.singleFunctor C 0)
        (H₀.shiftIso (-n) n 0 (by ring))
    d.hom.app Y ≫
      (DerivedCategory.Plus.singleFunctorCompHomologyFunctorIso 0).hom.app Y =
    (DerivedCategory.Plus.singleFunctorCompHomologyFunctorIso n).hom.app Y := by
  have hσ : DerivedCategory.Plus.ι.map
      (((DerivedCategory.Plus.singleFunctors C).shiftIso (-n) n 0 (by simp)).hom.app Y) =
      (DerivedCategory.Plus.ι.commShiftIso (-n)).hom.app
        ((DerivedCategory.Plus.singleFunctor C 0).obj Y) ≫
      (((DerivedCategory.singleFunctors C).shiftIso (-n) n 0 (by simp)).hom.app Y) := by
    erw [SingleFunctors.map_lift_shiftIso_hom_app]
    simp
    rfl
  have hσ' : ShiftedHom.map
      (((DerivedCategory.Plus.singleFunctors C).shiftIso (-n) n 0 (by simp)).inv.app Y)
      DerivedCategory.Plus.ι =
      (((DerivedCategory.singleFunctors C).shiftIso (-n) n 0 (by simp)).inv.app Y) := by
    change DerivedCategory.Plus.ι.map _ ≫ _ = _
    rw [← cancel_mono
      (((DerivedCategory.singleFunctors C).shiftIso (-n) n 0 (by simp)).hom.app Y)]
    erw [Category.assoc, ← hσ, ← CategoryTheory.Functor.map_comp]
    simp
    rfl
  change (DerivedCategory.Plus.homologyFunctor C 0).shiftMap
      (((DerivedCategory.Plus.singleFunctors C).shiftIso (-n) n 0 (by simp)).inv.app Y)
      n 0 (by simp) ≫ _ = _
  have ht : (DerivedCategory.Plus.homologyFunctor C 0).shiftMap
      (((DerivedCategory.Plus.singleFunctors C).shiftIso (-n) n 0 (by simp)).inv.app Y)
      n 0 (by simp) =
      (DerivedCategory.homologyFunctor C 0).shiftMap
        (ShiftedHom.map
          (((DerivedCategory.Plus.singleFunctors C).shiftIso (-n) n 0 (by simp)).inv.app Y)
          DerivedCategory.Plus.ι) n 0 (by simp) := by
    -- Unfold the generated wrapper of Mathlib's composition shift-sequence instance.
    simp only [Functor.shiftMap, ShiftedHom.map, DerivedCategory.Plus.homologyFunctor,
      Functor.shift, Functor.shiftIso,
      DerivedCategory.Plus.instShiftSequenceHomologyFunctorOfNatInt,
      DerivedCategory.Plus.instShiftSequenceHomologyFunctorOfNatInt._aux_1,
      Functor.ShiftSequence.instCompOfCommShift, Functor.ShiftSequence.leftComp,
      Functor.ShiftSequence.sequence, Functor.ShiftSequence.shiftIso,
      Iso.trans_hom, Iso.symm_hom, Functor.isoWhiskerRight_hom,
      Functor.isoWhiskerLeft_hom, NatTrans.comp_app,
      Functor.whiskerRight_app, Functor.whiskerLeft_app,
      Functor.associator_hom_app, Functor.associator_inv_app,
      CategoryTheory.Functor.comp_obj, CategoryTheory.Functor.map_comp,
      Category.id_comp, Category.assoc]
    with_unfolding_all
      change _ ≫ 𝟙 _ ≫ _ = _
    erw [Category.id_comp]
    rfl
  rw [ht, hσ']
  exact derived_comparison Y n
