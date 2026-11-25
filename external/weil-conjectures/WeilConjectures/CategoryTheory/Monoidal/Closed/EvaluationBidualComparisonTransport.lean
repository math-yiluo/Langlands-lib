/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.Mathlib.CategoryTheory.Monoidal.Closed.Basic
public import WeilConjectures.Mathlib.CategoryTheory.Monoidal.Rigid.Braided
public import WeilConjectures.CategoryTheory.ObjectProperty.Duality
public import Mathlib.CategoryTheory.ObjectProperty.ClosedUnderIsomorphisms

/-! # Transport of evaluation and the specified double-dual map

Source: Weil conjectures blueprint, sec-six-functors/sk-prop-sf-rf-shriek-preservation,
proposition-six-operations-dctf--15, final proof paragraph
(blueprint: lem-sf-evaluation-bidual-comparison-transport).

The internal Hom, its evaluation-transpose comparison, and its double-dual morphism
are the existing closed-category constructions. Only the full subcategories are
assumed equivalent; the ambient functor need not be fully faithful.
-/

@[expose] public section

set_option autoImplicit false

universe u v u' v'

open CategoryTheory MonoidalCategory MonoidalClosed Opposite

namespace CategoryTheory.MonoidalClosed

variable {C : Type u} {C' : Type u'} [Category.{v} C] [Category.{v'} C']
  [MonoidalCategory C] [MonoidalCategory C'] [MonoidalClosed C] [MonoidalClosed C']

/-- The specified comparison `F [K,W] ≅ [FK,W']`: the evaluation-transpose comparison
followed by the internal Hom of the chosen coefficient isomorphism. Its inverse uses only
invertibility of the comparison at this particular `K`.
Source: blueprint proposition-six-operations-dctf--15, final proof paragraph
(blueprint: lem-sf-evaluation-bidual-comparison-transport). -/
noncomputable def evaluationDualComparison (F : C ⥤ C') [F.LaxMonoidal]
    {W : C} {W' : C'} (w : F.obj W ≅ W') (K : C)
    (hβ : IsIso ((Functor.LaxMonoidal.ihomComparison F K).app W)) :
    F.obj ((ihom K).obj W) ≅ (ihom (F.obj K)).obj W' :=
  @asIso _ _ _ _ ((Functor.LaxMonoidal.ihomComparison F K).app W) hβ ≪≫
    (ihom (F.obj K)).mapIso w

private lemma comparison_ev (F : C ⥤ C') [F.LaxMonoidal]
    {W : C} {W' : C'} (w : F.obj W ≅ W') (K : C)
    (hβ : IsIso ((Functor.LaxMonoidal.ihomComparison F K).app W)) :
    F.obj K ◁ (evaluationDualComparison F w K hβ).hom ≫ (ihom.ev (F.obj K)).app W' =
      Functor.LaxMonoidal.μ F K _ ≫ F.map ((ihom.ev K).app W) ≫ w.hom := by
  dsimp only [evaluationDualComparison, Iso.trans_hom, asIso_hom, Functor.mapIso_hom]
  rw [← uncurry_eq, uncurry_natural_right, uncurry_eq,
    Functor.LaxMonoidal.ihomComparison_ev, Category.assoc]

private lemma comparison_natural (F : C ⥤ C') [F.LaxMonoidal]
    {W : C} {W' : C'} (w : F.obj W ≅ W') {K L : C} (f : L ⟶ K)
    (hK : IsIso ((Functor.LaxMonoidal.ihomComparison F K).app W))
    (hL : IsIso ((Functor.LaxMonoidal.ihomComparison F L).app W)) :
    F.map ((pre f).app W) ≫ (evaluationDualComparison F w L hL).hom =
      (evaluationDualComparison F w K hK).hom ≫ (pre (F.map f)).app W' := by
  dsimp only [evaluationDualComparison, Iso.trans_hom, asIso_hom, Functor.mapIso_hom]
  rw [← Category.assoc, Functor.LaxMonoidal.map_pre_app_comp_ihomComparison_app,
    Category.assoc, pre_comm_ihom_map, Category.assoc]

private lemma comparison_bidual [SymmetricCategory C] [SymmetricCategory C']
    (F : C ⥤ C') [F.Braided] {W : C} {W' : C'} (w : F.obj W ≅ W') (K : C)
    (hK : IsIso ((Functor.LaxMonoidal.ihomComparison F K).app W))
    (hDK : IsIso ((Functor.LaxMonoidal.ihomComparison F ((ihom K).obj W)).app W)) :
    toIhomIhom W' (F.obj K) = F.map (toIhomIhom W K) ≫
      (evaluationDualComparison F w ((ihom K).obj W) hDK).hom ≫
      (pre (evaluationDualComparison F w K hK).inv).app W' := by
  have h : F.map (toIhomIhom W K) ≫
      (evaluationDualComparison F w ((ihom K).obj W) hDK).hom =
      toIhomIhom W' (F.obj K) ≫
        (pre (evaluationDualComparison F w K hK).hom).app W' := by
    apply uncurry_injective
    rw [uncurry_natural_left, uncurry_eq, comparison_ev,
      uncurry_pre_app, uncurry_toIhomIhom,
      BraidedCategory.braiding_naturality_left_assoc, comparison_ev,
      Functor.LaxMonoidal.μ_natural_right_assoc, ← F.map_comp_assoc,
      ← uncurry_eq, uncurry_toIhomIhom, F.map_comp,
      ← Functor.LaxBraided.braided_assoc]
    simp only [Category.assoc]
  rw [← Category.assoc, h, Category.assoc, ← NatTrans.comp_app, ← pre_map,
    Iso.inv_hom_id, pre_id, NatTrans.id_app, Category.comp_id]

/-- Transport duality on replete full subcategories using the canonical evaluation comparison.
Source: blueprint proposition-six-operations-dctf--15, final proof paragraph
(blueprint: lem-sf-evaluation-bidual-comparison-transport).

Proof plan:
1. Use naturality of the tensor-Hom adjunction to commute untransposition with
   precomposition and internal-Hom maps; untransposition is injective.
2. Untranspose `ihomComparison` and postcompose with `w`. This gives the evaluation
   equation, with the tensorator explicitly restored.
3. For a map `L → K`, untranspose the two naturality composites. Evaluation naturality
   and tensorator naturality identify them, giving the natural comparison below.
4. For `P` in the target subcategory, use essential surjectivity to choose `FK ≅ P`.
   Apply the target dual functor and the comparison at `K`; repleteness and preservation
   of the source subcategory show that the target dual is again in the target subcategory.
5. Untranspose `F(δ_K)` followed by the comparison at `DK`. The evaluation equation,
   naturality of the tensorator and preservation of symmetry identify its untranspose
   with evaluation at `FK` after the symmetry and `c_K ⊗ 1`.
6. Untransposing `δ'_{FK}` followed by precomposition with `c_K` gives the same map.
   Injectivity and the inverse of `c_K` give the displayed double-dual equation.
7. Untranspose the two composites expressing naturality of the specified `δ'` for
   any ambient map. Evaluation and symmetry naturality identify them.
8. If the source `δ_K` are invertible, the double-dual equation makes `δ'_{FK}`
   invertible. Essential surjectivity and step 7 give invertibility at every target object.
9. Restrict the target dual. Its right opposite is a quasi-inverse, with the natural
   double-dual isomorphisms as unit and counit. This proves anti-equivalence under
   the stated source anti-equivalence and invertible-biduality hypotheses.
-/
theorem evaluationBidualComparisonTransport
    [SymmetricCategory C] [SymmetricCategory C']
    (F : C ⥤ C') [F.Braided] {W : C} {W' : C'} (w : F.obj W ≅ W')
    (B : ObjectProperty C) (B' : ObjectProperty C')
    [B.IsClosedUnderIsomorphisms] [B'.IsClosedUnderIsomorphisms]
    (hD : ∀ K : C, B K → B ((ihom K).obj W))
    (hF : ∀ K : C, B K → B' (F.obj K))
    [(B'.lift (B.ι ⋙ F) (fun K ↦ hF K.obj K.property)).IsEquivalence]
    (hβ : ∀ (K : C), B K →
      IsIso ((Functor.LaxMonoidal.ihomComparison F K).app W)) :
    ∃ hD' : ∀ P : C', B' P → B' ((ihom P).obj W'),
      (∃ c : B.liftDual (internalHom.flip.obj W) hD ⋙
          B'.lift (B.ι ⋙ F) (fun K ↦ hF K.obj K.property) ≅
          (B'.lift (B.ι ⋙ F) (fun K ↦ hF K.obj K.property)).op ⋙
            B'.liftDual (internalHom.flip.obj W') hD',
        ∀ K : B.FullSubcategoryᵒᵖ,
          (c.hom.app K).hom = (evaluationDualComparison F w K.unop.obj
            (hβ K.unop.obj K.unop.property)).hom) ∧
      (∀ (K : C) (hK : B K),
        ((evaluationDualComparison F w K (hβ K hK)).hom ⊗ₘ 𝟙 (F.obj K)) ≫
            (β_ ((ihom (F.obj K)).obj W') (F.obj K)).hom ≫
            (ihom.ev (F.obj K)).app W' =
          Functor.LaxMonoidal.μ F ((ihom K).obj W) K ≫
            F.map ((β_ ((ihom K).obj W) K).hom ≫ (ihom.ev K).app W) ≫ w.hom ∧
        toIhomIhom W' (F.obj K) =
          F.map (toIhomIhom W K) ≫
            (evaluationDualComparison F w ((ihom K).obj W)
              (hβ ((ihom K).obj W) (hD K hK))).hom ≫
            (pre (evaluationDualComparison F w K (hβ K hK)).inv).app W') ∧
      ((B.liftDual (internalHom.flip.obj W) hD).IsEquivalence →
        (∀ (K : C), B K → IsIso (toIhomIhom W K)) →
        (B'.liftDual (internalHom.flip.obj W') hD').IsEquivalence ∧
          ∀ (P : C'), B' P → IsIso (toIhomIhom W' P)) := by
  classical
  let E := B'.lift (B.ι ⋙ F) (fun K ↦ hF K.obj K.property)
  have hD' : ∀ P : C', B' P → B' ((ihom P).obj W') := by
    intro P hP
    let K := E.objPreimage ⟨P, hP⟩
    let a : F.obj K.obj ≅ P := B'.ι.mapIso (E.objObjPreimageIso ⟨P, hP⟩)
    exact B'.prop_of_iso
      (evaluationDualComparison F w K.obj (hβ K.obj K.property) ≪≫
        ihomIsoOfIsoLeft a W') (hF _ (hD _ K.property))
  refine ⟨hD', ?_, ?_, ?_⟩
  · refine ⟨NatIso.ofComponents (fun K ↦ B'.isoMk
        (evaluationDualComparison F w K.unop.obj
          (hβ K.unop.obj K.unop.property))) ?_, fun K ↦ rfl⟩
    intro K L f
    apply B'.hom_ext
    exact comparison_natural F w f.unop.hom
      (hβ K.unop.obj K.unop.property) (hβ L.unop.obj L.unop.property)
  · intro K hK
    constructor
    · rw [tensorHom_id, BraidedCategory.braiding_naturality_left_assoc, comparison_ev,
        ← Functor.LaxBraided.braided_assoc, F.map_comp, Category.assoc]
    · exact comparison_bidual F w K (hβ K hK) (hβ _ (hD K hK))
  · intro _ hδ
    have hδF : ∀ K : C, B K → IsIso (toIhomIhom W' (F.obj K)) := by
      intro K hK
      have := hδ K hK
      rw [comparison_bidual F w K (hβ K hK) (hβ _ (hD K hK))]
      infer_instance
    have hδ' : ∀ P : C', B' P → IsIso (toIhomIhom W' P) := by
      intro P hP
      let K := E.objPreimage ⟨P, hP⟩
      let a : F.obj K.obj ≅ P := B'.ι.mapIso (E.objObjPreimageIso ⟨P, hP⟩)
      have := hδF K.obj K.property
      have h : toIhomIhom W' P = a.inv ≫ toIhomIhom W' (F.obj K.obj) ≫
          (pre ((pre a.hom).app W')).app W' := by
        rw [← toIhomIhom_naturality, Iso.inv_hom_id_assoc]
      rw [h]
      infer_instance
    exact ⟨(B'.liftDualEquivalence (internalHom.flip.obj W') hD'
      (toIhomIhomNatTrans W') hδ').isEquivalence_functor, hδ'⟩

end CategoryTheory.MonoidalClosed
