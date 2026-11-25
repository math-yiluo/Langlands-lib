/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.CategoryTheory.RingedKoszulSystem
import WeilConjectures.CategoryTheory.RingedHomTensorUnitNormalization
import WeilConjectures.CategoryTheory.RingedKoszulDualizable

/-! # Evaluation for the finite strict Koszul stages

Source: Stacks Project, sites-cohomology.tex, Tag 0A0A; more-algebra.tex, Tag 0913.
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u v w

open CategoryTheory CategoryTheory.Limits Opposite

namespace CategoryTheory

private theorem inverse_square {D : Type v} [Category.{w} D]
    {A B A' B' : D} (e : A ≅ B) (e' : A' ≅ B')
    (f : A ⟶ A') (g : B ⟶ B') (h : f ≫ e'.hom = e.hom ≫ g) :
    g ≫ e'.inv = e.inv ≫ f := by
  apply (cancel_mono e'.hom).mp
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
  rw [h, Iso.inv_hom_id_assoc]

private theorem inverse_unit {D : Type v} [Category.{w} D]
    {A B K L : D} (e : A ≅ B) (a : K ⟶ L) (b : L ⟶ B) (f : K ⟶ A)
    (h : a ≫ b = f ≫ e.hom) : a ≫ b ≫ e.inv = f := by
  rw [← Category.assoc, h, Category.assoc, Iso.hom_inv_id, Category.comp_id]

variable {C : Type u} [SmallCategory C] {J : GrothendieckTopology C}
variable (O : Sheaf J CommRingCat.{u}) (r : ℕ)
variable (b : Fin r → (O.obj ⋙ forget CommRingCat).sections)

attribute [local irreducible] homComplexFunctor ringedComplexTensorEvaluation
  ringedKoszulProjection ringedKoszulDiagram ringedHomUnitEvaluationIso

/-- Finite-free evaluation, including transition, coefficient and unit compatibility.

Source: Stacks Project, sites-cohomology.tex, Tag 0A0A,
lemma-colim-and-lim-of-duals; more-algebra.tex, Tag 0913.
(auxiliary; not a blueprint node).

Proof: each positive two-term factor is bounded with dualizable unit terms.
The bounded-complex duality theorem and induction on the actual tensor diagram
therefore make every finite Koszul stage dualizable. Transport the tensor-Hom
adjunction along the signed comparison with the ordinary product Hom. Its canonical
tensor evaluation is invertible on these stages and natural in both variables,
so the evaluations assemble to an isomorphism from the strict tensor tower to
the Hom tower. Take its inverse. Coefficient naturality follows by cancellation.
For the projection P_m -> O[0], source naturality and the closed-category unit law
identify the tensor unit with precomposition by that projection. In degree zero
the signed adjunction has sign one, so its unit agrees with inverse evaluation
at one, giving the required unit equation. The empty tensor and zero or
invertible generators require no additional assumptions.
No colimit or inverse limit is taken in this statement. -/
theorem exists_ringedKoszul_finiteEvaluation :
    ∃ e : ∀ N : ringedSiteComplex O,
      (ringedKoszulDiagram O r b).op ⋙ (homComplexFunctor (R := O)).flip.obj N ≅
        (ringedKoszulTensorTower O r b).obj N,
      (∀ (N M : ringedSiteComplex O) (f : N ⟶ M) (m : ℕᵒᵖ),
        ((homComplexFunctor (R := O)).obj
          (op ((ringedKoszulDiagram O r b).obj m.unop))).map f ≫ (e M).hom.app m =
        (e N).hom.app m ≫ ((ringedKoszulTensorTower O r b).map f).app m) ∧
      (∀ (N : ringedSiteComplex O) (m : ℕᵒᵖ),
        (ringedHomUnitEvaluationIso O N).inv ≫
          ((homComplexFunctor (R := O)).map
            (ringedKoszulProjection O r b m.unop).op).app N ≫ (e N).hom.app m =
        ringedKoszulTensorUnitComponent O r b N m) := by
  have (N : ringedSiteComplex O) (m : ℕᵒᵖ) :
      IsIso (ringedComplexTensorEvaluation O ((ringedKoszulDiagram O r b).obj m.unop) N) :=
    ringedComplexTensorEvaluation_isIso O _ N (ringedKoszulStage_dualizable O r b m.unop)
  let a (N : ringedSiteComplex O) :
      ((ringedKoszulTensorTower O r b).obj N) ≅
        (ringedKoszulDiagram O r b).op ⋙ (homComplexFunctor (R := O)).flip.obj N :=
    NatIso.ofComponents
      (fun m ↦ asIso
        (ringedComplexTensorEvaluation O ((ringedKoszulDiagram O r b).obj m.unop) N))
      (fun f ↦ ringedComplexTensorEvaluation_source O
        ((ringedKoszulDiagram O r b).map f.unop) N)
  refine ⟨fun N ↦ (a N).symm, ?_, ?_⟩
  · intro N M f m
    exact inverse_square
      (asIso (ringedComplexTensorEvaluation O ((ringedKoszulDiagram O r b).obj m.unop) N))
      (asIso (ringedComplexTensorEvaluation O ((ringedKoszulDiagram O r b).obj m.unop) M))
      _ _ (ringedComplexTensorEvaluation_naturality O _ f)
  · intro N m
    apply inverse_unit
      (asIso (ringedComplexTensorEvaluation O ((ringedKoszulDiagram O r b).obj m.unop) N))
    change (ringedHomUnitEvaluationIso O N).inv ≫
        ((homComplexFunctor (R := O)).map
          (ringedKoszulProjection O r b m.unop).op).app N =
      ringedKoszulTensorUnitComponent O r b N m ≫
        ringedComplexTensorEvaluation O ((ringedKoszulDiagram O r b).obj m.unop) N
    rw [ringedKoszulTensorUnitComponent, ringedKoszulDualUnit,
      ← ringedComplexHomUnit_eq O (ringedSiteRingComplex O), Functor.map_comp]
    simp only [Category.assoc]
    erw [ringedComplexTensorEvaluation_source O
      (ringedKoszulProjection O r b m.unop) N]
    have hu := congrArg (fun z : N ⟶ homComplex (R := O) (ringedSiteRingComplex O) N ↦
        z ≫ ((homComplexFunctor (R := O)).map
          (ringedKoszulProjection O r b m.unop).op).app N)
      (ringedComplexTensorEvaluation_unit O N)
    rw [ringedComplexHomUnit_eq O N] at hu
    simpa only [Category.assoc] using hu.symm

end CategoryTheory
