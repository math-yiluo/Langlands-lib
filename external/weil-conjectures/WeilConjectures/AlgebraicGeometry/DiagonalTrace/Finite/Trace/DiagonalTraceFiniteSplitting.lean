/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.DiagonalTrace.Presentation.DiagonalTowerTracePresentations

import WeilConjectures.AlgebraicGeometry.DiagonalTrace.Finite.Trace.DiagonalTraceFiniteUnitCohomology
import WeilConjectures.AlgebraicGeometry.DiagonalTrace.Finite.Trace.DiagonalTraceFiniteChernCohomology
import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor

/-! # The finite evaluation of the normalized projective-line splitting

Source: blueprint latest, diagonal-tower trace proof, paragraph (1).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option genSizeOf false
set_option genInjectivity false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.ProEtale.DiagonalTrace

open SpTowerClasses

private lemma isIso_map_desc_of_isZero_right
    {C D : Type*} [Category C] [Category D] [Preadditive C] [Preadditive D]
    (F : C ⥤ D) [F.Additive] {U V W : C} [HasBinaryBiproduct U V]
    (a : U ⟶ W) (b : V ⟶ W) (hV : IsZero (F.obj V)) [IsIso (F.map a)] :
    IsIso (F.map (biprod.desc a b)) := by
  have hzero : F.map (biprod.snd ≫ biprod.inr : U ⊞ V ⟶ U ⊞ V) = 0 := by
    rw [F.map_comp, hV.eq_of_src (F.map biprod.inr) 0, comp_zero]
  have hinl : IsIso (F.map (biprod.inl : U ⟶ U ⊞ V)) := by
    refine ⟨⟨F.map biprod.fst, ?_, ?_⟩⟩
    · rw [← F.map_comp, biprod.inl_fst, F.map_id]
    · have ht := congrArg F.map (biprod.total (X := U) (Y := V))
      rw [F.map_add, hzero, add_zero, F.map_id, F.map_comp] at ht
      exact ht
  have hcomp : IsIso (F.map (biprod.inl : U ⟶ U ⊞ V) ≫
      F.map (biprod.desc a b)) := by
    rw [← F.map_comp, biprod.inl_desc]
    infer_instance
  exact IsIso.of_isIso_comp_left (F.map (biprod.inl : U ⟶ U ⊞ V)) _

private lemma isIso_map_desc_of_isZero_left
    {C D : Type*} [Category C] [Category D] [Preadditive C] [Preadditive D]
    (F : C ⥤ D) [F.Additive] {U V W : C} [HasBinaryBiproduct U V]
    (a : U ⟶ W) (b : V ⟶ W) (hU : IsZero (F.obj U)) [IsIso (F.map b)] :
    IsIso (F.map (biprod.desc a b)) := by
  have hzero : F.map (biprod.fst ≫ biprod.inl : U ⊞ V ⟶ U ⊞ V) = 0 := by
    rw [F.map_comp, hU.eq_of_src (F.map biprod.inl) 0, comp_zero]
  have hinr : IsIso (F.map (biprod.inr : V ⟶ U ⊞ V)) := by
    refine ⟨⟨F.map biprod.snd, ?_, ?_⟩⟩
    · rw [← F.map_comp, biprod.inr_snd, F.map_id]
    · have ht := congrArg F.map (biprod.total (X := U) (Y := V))
      rw [F.map_add, hzero, zero_add, F.map_id, F.map_comp] at ht
      exact ht
  have hcomp : IsIso (F.map (biprod.inr : V ⟶ U ⊞ V) ≫
      F.map (biprod.desc a b)) := by
    rw [← F.map_comp, biprod.inr_desc]
    infer_instance
  exact IsIso.of_isIso_comp_left (F.map (biprod.inr : V ⟶ U ⊞ V)) _

/-- At one positive finite level the actual unit/Chern map is invertible.

Source: `sk-prop-diagonal-tower-trace.proof.md`, paragraph (1), and
`lemma-cohomology-projective-line-trace`, decomposition (G2).
(blueprint: lem-sfb-diagonal-trace-finite-splitting).

Proof: use the normalized evaluation comparison for the geometric system
adjunction to evaluate the unit summand. It becomes the ordinary finite
coefficient adjunction unit. Evaluate the integral Cartier extension and its
Kummer boundary using p.finiteX. The positive Cartier sign and the sectionwise
root-to-tensor comparison identify the evaluated Chern arrow with the usual
finite Kummer class of the pullback of O(1). Evaluation preserves shifts, the
line tensor/Hom equivalence, and its unit and counit, so the evaluated second
summand is the negative twist of that same Chern adjunct. The resulting map is
therefore the finite projective-line decomposition (G2), transported along
p.model.model and its equation over S. That map is invertible by
geoP1Cohomology, with coefficient ring the level n+1 quotient of Z_l. The
hypothesis hS makes l^(n+1) invertible, and n+1 is positive even for n=0.
Conjugation by the source and target comparison isomorphisms preserves
invertibility, proving the assertion for the specified model and its actual bq.
The argument uses no claim that evaluations detect equality of derived arrows. -/
theorem diagonalTrace_finite_splitting
    (l : ℕ) [Fact l.Prime] {X S : Scheme.{u}}
    [IsNoetherian X] [IsNoetherian S]
    [DiagonalTraceLocalizations l X] [DiagonalTraceLocalizations l S]
    {f : X ⟶ S} (p : Presentation l (ULift.{u} (Padic l)) f)
    (hS : IsUnit (l : Γ(S, ⊤))) (n : ℕ) :
    IsIso ((SpTowerShriek.Ev l (ULift.{u} (Padic l)) S n).map
      (p.model.bq l (ULift.{u} (Padic l)))) := by
  let E := ULift.{u} (Padic l)
  let ev := SpTowerShriek.ev l E S n
  rw [DerivedCategory.isIso_iff]
  intro q
  let H := ev.mapDerivedCategory ⋙ DerivedCategory.homologyFunctor _ q
  change IsIso (H.map (p.model.bq l E))
  by_cases hq : q = 2
  · subst q
    have hu : IsZero (H.obj (unit S (Arings l E S))) := by
      apply ev.isZero_homologyFunctor_mapDerivedCategory_obj
      have hunit : (unit S (Arings l E S)).IsLE 0 := by
        change ((DerivedCategory.singleFunctor _ 0).obj _).IsLE 0
        infer_instance
      exact DerivedCategory.isZero_of_isLE _ 0 2 (by decide) (hX := hunit)
    have : IsIso (H.map (p.model.second l E)) :=
      diagonalTrace_finite_chern_cohomology l E p.model p.finiteX hS n
    exact isIso_map_desc_of_isZero_left H
      (unitArrow l E p.model.coefficientPullback) (p.model.second l E) hu
  · have hv : IsZero (H.obj ((inverseLine l E p.chernS)⟦(-2 : ℤ)⟧)) := by
      apply ev.isZero_homologyFunctor_mapDerivedCategory_obj
      have : DerivedCategory.TStructure.t.IsGE (inverseLine l E p.chernS) 0 := by
        change ((DerivedCategory.singleFunctor _ 0).obj _).IsGE 0
        infer_instance
      have : DerivedCategory.TStructure.t.IsLE (inverseLine l E p.chernS) 0 := by
        change ((DerivedCategory.singleFunctor _ 0).obj _).IsLE 0
        infer_instance
      have hge : ((inverseLine l E p.chernS)⟦(-2 : ℤ)⟧).IsGE 2 :=
        DerivedCategory.TStructure.t.isGE_shift _ 0 (-2) 2
      have hle : ((inverseLine l E p.chernS)⟦(-2 : ℤ)⟧).IsLE 2 :=
        DerivedCategory.TStructure.t.isLE_shift _ 0 (-2) 2
      rcases lt_or_gt_of_ne hq with hlt | hgt
      · exact DerivedCategory.isZero_of_isGE _ 2 q hlt (hX := hge)
      · exact DerivedCategory.isZero_of_isLE _ 2 q hgt (hX := hle)
    have : IsIso (H.map (unitArrow l E p.model.coefficientPullback)) :=
      diagonalTrace_finite_unit_cohomology l E p.base p.model.model
        p.model.over_eq p.model.geometry p.model.coefficientPullback hS n q hq
    exact isIso_map_desc_of_isZero_right H
      (unitArrow l E p.model.coefficientPullback) (p.model.second l E) hv

end AlgebraicGeometry.ProEtale.DiagonalTrace
