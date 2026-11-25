/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.CategoryTheory.CechResolutionDoubleComplex
public import Mathlib.Algebra.Homology.Functor
import WeilConjectures.CategoryTheory.FormalCoproductEvaluationHomology

/-!
# Homology and the Čech complex of a complex of presheaves

Source: blueprint lemma-coherent-base-change-invertible-sheaves--1, Step 2, product cohomology
calculation.
-/

@[expose] public section

universe u v

namespace CategoryTheory

open Limits

private noncomputable def evalHomologyIso
    {C : Type u} [Category.{v} C]
    (K : CochainComplex (C ⥤ AddCommGrpCat.{v}) ℕ) (q : ℕ) :
    K.homology q ≅ K.asFunctor ⋙ HomologicalComplex.homologyFunctor _ (ComplexShape.up ℕ) q :=
  NatIso.ofComponents
    (fun X ↦ ((K.sc q).mapHomologyIso ((evaluation C AddCommGrpCat).obj X)).symm)
    (by
      intro X Y f
      let τ : (evaluation C AddCommGrpCat).obj X ⟶
          (evaluation C AddCommGrpCat).obj Y :=
        { app := fun P ↦ P.map f
          naturality := fun P Q α ↦ (α.naturality f).symm }
      have h := NatTrans.app_homology τ (K.sc q)
      dsimp [τ] at h
      change (K.sc q).homology.map f ≫
        ((K.sc q).mapHomologyIso ((evaluation C AddCommGrpCat).obj Y)).inv = _
      rw [h]
      simp only [Category.assoc, Iso.hom_inv_id, Category.comp_id]
      rfl)

set_option backward.isDefEq.respectTransparency false in
/-- Taking vertical homology of the Čech bicomplex commutes with the Čech construction.

Source: blueprint lemma-coherent-base-change-invertible-sheaves--1, Step 2.
Proof: in Čech degree p, evaluate K on each product indexed by a tuple of p+1
covering indices. The resulting vertical complex is the product of those evaluation
complexes. The kernel of a product of homomorphisms is the product of the kernels.
The image is the product of the images: choose a preimage for each component.
The quotient of the product of kernels by the product of images is therefore the
product of the individual homology groups. These canonical identifications commute
with projections and with restriction maps, since the maps on homology are induced
by the same maps on cycles. In particular they commute with each Čech coface and
its alternating sum. Assemble them and their inverses into an isomorphism of
complexes. The empty indexing family gives zero products, and the same argument
applies in degree zero, where the incoming differential is zero.
(blueprint: lem-sc-cech-complex-homology) -/
theorem cechComplexFunctor_homology
    {C : Type u} [Category.{v} C] [HasFiniteProducts C]
    {ι : Type v} (U : ι → C) (K : CochainComplex (Cᵒᵖ ⥤ AddCommGrpCat.{v}) ℕ)
    (q : ℕ) :
    Nonempty
      (((HomologicalComplex.homologyFunctor _ (ComplexShape.up ℕ) q).mapHomologicalComplex
        (ComplexShape.up ℕ)).obj
          (HomologicalComplex₂.flip
            (((cechComplexFunctor U).mapHomologicalComplex (ComplexShape.up ℕ)).obj K)) ≅
      (cechComplexFunctor U).obj
        (K.asFunctor ⋙ HomologicalComplex.homologyFunctor _ (ComplexShape.up ℕ) q)) := by
  have : ∀ n, (cechComplexFunctor U ⋙
      HomologicalComplex.eval AddCommGrpCat (ComplexShape.up ℕ) n).PreservesHomology :=
    fun n ↦ formalCoproductEval_preservesHomology _
  let S := K.sc q
  let F (n : ℕ) := cechComplexFunctor U ⋙
    HomologicalComplex.eval AddCommGrpCat (ComplexShape.up ℕ) n
  let h := evalHomologyIso K q
  let e (n : ℕ) := S.mapHomologyIso (F n) ≪≫ (F n).mapIso h
  refine ⟨HomologicalComplex.Hom.isoOfComponents e ?_⟩
  intro i j hij
  let τ : F i ⟶ F j :=
    { app := fun P ↦ ((cechComplexFunctor U).obj P).d i j
      naturality := fun P Q α ↦ ((cechComplexFunctor U).map α).comm i j }
  have hh := NatTrans.app_homology τ S
  have hn := τ.naturality h.hom
  dsimp [τ] at hh hn
  change (S.mapHomologyIso (F i)).hom ≫ (F i).map h.hom ≫ _ = _
  dsimp only [S, HomologicalComplex.homology] at hn ⊢
  rw [hn]
  dsimp only [S] at hh
  rw [hh]
  simp only [Category.assoc, Iso.hom_inv_id_assoc]
  rfl

end CategoryTheory
