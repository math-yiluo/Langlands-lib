/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.CategoryTheory.Adjunction.TensorInvertible
public import WeilConjectures.CategoryTheory.Adjunction.ProjectionTensorMap
/-! # The invertible-factor co-projection is the inverse tensor mate

The evaluation, associativity and unit calculations in the blueprint's co-projection
Hom chain identify the right-adjoint comparison with the inverse tensor mate.
-/

@[expose] public noncomputable section
set_option autoImplicit false
open CategoryTheory CategoryTheory.MonoidalCategory
namespace CategoryTheory.Adjunction
variable {C D : Type*} [Category C] [Category D] [MonoidalCategory C] [MonoidalCategory D]
  {F : C ⥤ D} {G : D ⥤ C} (adj : F ⊣ G) (P : D ⥤ C) [P.Monoidal]
  {L M : D} (e : M ⊗ L ≅ 𝟙_ D) (e' : L ⊗ M ≅ 𝟙_ D)
  (pf : F ⋙ tensorRight M ≅ tensorRight (P.obj M) ⋙ F)
  (pfL : F ⋙ tensorRight L ≅ tensorRight (P.obj L) ⋙ F)

private theorem tensorProjection_evaluation
    (π : ∀ N : D, F ⋙ tensorRight N ≅ tensorRight (P.obj N) ⋙ F)
    (hn : ∀ (Z : C) {N N' : D} (f : N ⟶ N'),
      F.obj Z ◁ f ≫ (π N').hom.app Z =
        (π N).hom.app Z ≫ F.map (Z ◁ P.map f))
    (ha : ∀ (Z : C) (N N' : D),
      (π N).hom.app Z ▷ N' ≫ (π N').hom.app (Z ⊗ P.obj N) ≫
        F.map (α_ Z (P.obj N) (P.obj N')).hom =
      (α_ (F.obj Z) N N').hom ≫ (π (N ⊗ N')).hom.app Z ≫
        F.map (Z ◁ (Functor.Monoidal.μIso P N N').inv))
    (hu : ∀ Z : C, (π (𝟙_ D)).hom.app Z ≫
      F.map (Z ◁ (Functor.Monoidal.εIso P).inv ≫ (ρ_ Z).hom) =
        (ρ_ (F.obj Z)).hom) (Z : C) :
    (π M).inv.app (Z ⊗ P.obj L) ≫ (π L).inv.app Z ▷ M ≫
        (α_ (F.obj Z) L M).hom ≫ F.obj Z ◁ e'.hom ≫ (ρ_ (F.obj Z)).hom =
      F.map ((α_ Z (P.obj L) (P.obj M)).hom ≫
        Z ◁ (Functor.Monoidal.μIso P L M ≪≫ P.mapIso e' ≪≫
          (Functor.Monoidal.εIso P).symm).hom ≫ (ρ_ Z).hom) := by
  apply (cancel_epi ((π L).hom.app Z ▷ M ≫
    (π M).hom.app (Z ⊗ P.obj L))).1
  simp only [Category.assoc, Iso.hom_inv_id_app_assoc,
    ← comp_whiskerRight_assoc, Iso.hom_inv_id_app, id_whiskerRight, Category.id_comp]
  rw [F.map_comp, F.map_comp]
  rw [reassoc_of% (ha Z L M)]
  simp only [Iso.trans_hom, Iso.symm_hom, Functor.mapIso_hom,
    whiskerLeft_comp, F.map_comp, Category.assoc]
  rw [← F.map_comp_assoc, ← whiskerLeft_comp, Iso.inv_hom_id,
    whiskerLeft_id]
  rw [F.map_id (Z ⊗ P.obj (L ⊗ M))]
  erw [Category.id_comp]
  rw [← reassoc_of% (hn Z e'.hom)]
  rw [← F.map_comp, hu Z]

private theorem tensorCoprojection_inverse
    (heval : ∀ Z : C,
      pf.inv.app (Z ⊗ P.obj L) ≫ pfL.inv.app Z ▷ M ≫
        (α_ (F.obj Z) L M).hom ≫ F.obj Z ◁ e'.hom ≫ (ρ_ (F.obj Z)).hom =
      F.map ((α_ Z (P.obj L) (P.obj M)).hom ≫
        Z ◁ (Functor.Monoidal.μIso P L M ≪≫ P.mapIso e' ≪≫
          (Functor.Monoidal.εIso P).symm).hom ≫ (ρ_ Z).hom))
    (K : D) :
    (adj.tensorRightCompIsoOfTensorIso P e e' pf).inv.app K =
      adj.homEquiv _ _ (pfL.inv.app (G.obj K) ≫ adj.counit.app K ▷ L) := by
  let a := (tensorRightEquivalenceOfTensorIso e e').toAdjunction
  let b := (tensorRightEquivalenceOfTensorIso
    (Functor.Monoidal.μIso P M L ≪≫ P.mapIso e ≪≫
      (Functor.Monoidal.εIso P).symm)
    (Functor.Monoidal.μIso P L M ≪≫ P.mapIso e' ≪≫
      (Functor.Monoidal.εIso P).symm)).toAdjunction
  let τ := adj.homEquiv _ _ (pfL.inv.app (G.obj K) ≫ adj.counit.app K ▷ L)
  apply (((adj.comp a).ofNatIsoLeft pf).homEquiv _ K).symm.injective
  change (((adj.comp a).ofNatIsoLeft pf).homEquiv _ K).symm
      ((rightAdjointUniq (b.comp adj) ((adj.comp a).ofNatIsoLeft pf)).hom.app K) = _
  rw [homEquiv_symm_rightAdjointUniq_hom_app]
  rw [homEquiv_counit]
  simp only [comp_counit_app, ofNatIsoLeft_counit, NatTrans.comp_app,
    Functor.whiskerLeft_app]
  change F.map (b.counit.app (G.obj K)) ≫ adj.counit.app K =
    F.map (τ ▷ P.obj M) ≫ pf.inv.app (G.obj (K ⊗ L)) ≫
      (adj.counit.app (K ⊗ L) ▷ M) ≫ a.counit.app K
  have hn := pf.inv.naturality τ
  change F.map (τ ▷ P.obj M) ≫ pf.inv.app (G.obj (K ⊗ L)) =
    pf.inv.app (G.obj K ⊗ P.obj L) ≫ F.map τ ▷ M at hn
  rw [reassoc_of% hn]
  have ht : F.map τ ≫ adj.counit.app (K ⊗ L) =
      pfL.inv.app (G.obj K) ≫ adj.counit.app K ▷ L := by
    exact (adj.homEquiv _ _).symm_apply_apply _
  rw [← comp_whiskerRight_assoc, ht, comp_whiskerRight]
  simp only [Category.assoc]
  change F.map ((α_ (G.obj K) (P.obj L) (P.obj M)).hom ≫
      G.obj K ◁ (Functor.Monoidal.μIso P L M ≪≫ P.mapIso e' ≪≫
        (Functor.Monoidal.εIso P).symm).hom ≫ (ρ_ (G.obj K)).hom) ≫
        adj.counit.app K =
    pf.inv.app (G.obj K ⊗ P.obj L) ≫ pfL.inv.app (G.obj K) ▷ M ≫
      (adj.counit.app K ▷ L) ▷ M ≫
        (α_ K L M).hom ≫ K ◁ e'.hom ≫ (ρ_ K).hom
  rw [reassoc_of% (associator_naturality_left (adj.counit.app K) L M)]
  rw [← reassoc_of% (whisker_exchange (adj.counit.app K) e'.hom)]
  rw [rightUnitor_naturality]
  simpa only [Category.assoc] using
    congrArg (· ≫ adj.counit.app K) (heval (G.obj K)).symm

/-- The inverse of the invertible-factor right-adjoint comparison is the canonical
tensor mate. The projection formula is assumed natural, associative, and right unital.
Source: current blueprint sk-lem-coprojection, displayed Hom calculation
(blueprint: lem-pur-invertible-coprojection-tensor-mate).
Proof: transpose the comparison under the composite tensor adjunction. Its counit is
evaluation followed by the right unitor. Naturality of the projection formula moves
the transpose across projection at the inverse factor. Associativity, naturality at
the evaluation and right unitality identify the two counits. Injectivity of the
adjunction Hom equivalence then identifies the original maps. -/
theorem tensorRightCompIso_inv_eq_projectionTensorMap
    (π : ∀ N : D, F ⋙ tensorRight N ≅ tensorRight (P.obj N) ⋙ F)
    (hn : ∀ (Z : C) {N N' : D} (f : N ⟶ N'),
      F.obj Z ◁ f ≫ (π N').hom.app Z =
        (π N).hom.app Z ≫ F.map (Z ◁ P.map f))
    (ha : ∀ (Z : C) (N N' : D),
      (π N).hom.app Z ▷ N' ≫ (π N').hom.app (Z ⊗ P.obj N) ≫
        F.map (α_ Z (P.obj N) (P.obj N')).hom =
      (α_ (F.obj Z) N N').hom ≫ (π (N ⊗ N')).hom.app Z ≫
        F.map (Z ◁ (Functor.Monoidal.μIso P N N').inv))
    (hu : ∀ Z : C, (π (𝟙_ D)).hom.app Z ≫
      F.map (Z ◁ (Functor.Monoidal.εIso P).inv ≫ (ρ_ Z).hom) =
        (ρ_ (F.obj Z)).hom) (K : D) :
    (adj.tensorRightCompIsoOfTensorIso P e e' (π M)).inv.app K =
      adj.projectionTensorMap (fun Z N ↦ (π N).hom.app Z) K L := by
  unfold projectionTensorMap
  rw [show inv ((π L).hom.app (G.obj K)) = (π L).inv.app (G.obj K) from
    IsIso.inv_eq_of_hom_inv_id (Iso.hom_inv_id ((π L).app (G.obj K)))]
  exact tensorCoprojection_inverse adj P e e' (π M) (π L)
    (fun Z ↦ tensorProjection_evaluation P e' π hn ha hu Z) K

end CategoryTheory.Adjunction
