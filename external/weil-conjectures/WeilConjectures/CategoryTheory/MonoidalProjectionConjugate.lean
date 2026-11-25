/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.Mathlib.CategoryTheory.Monoidal.Rigid.OfEquivalence
public import Mathlib.CategoryTheory.Adjunction.Mates

/-! # Normalization of the dualizable projection comparison

Source: Stacks Project, Cohomology, Tag 0B54 (projection formula for perfect objects),
and Duality for Schemes, Tag 0A9T (the tensor-Hom argument).
(blueprint: lem-sc-monoidal-projection-conjugate).
-/

@[expose] public section

set_option autoImplicit false
universe v₁ v₂ u₁ u₂

open CategoryTheory MonoidalCategory Functor.LaxMonoidal Functor.OplaxMonoidal

namespace CategoryTheory

set_option backward.isDefEq.respectTransparency.types false in
/-- The conjugate of the tensorator at the dual is the canonical projection map.
Source: Stacks Project, Cohomology, Tag 0B54, and Duality for Schemes, Tag 0A9T.
(blueprint: lem-sc-monoidal-projection-conjugate).
Proof: expand conjugation under the two composite adjunctions. Their Hom equivalences
are the composites of the tensor-Hom equivalences with `a.homEquiv`. Transpose the
claimed equality under `a`. The remaining expression inserts coevaluation, applies
F to evaluation, and then applies the counit of a. Naturality of the counit removes
its intervening unit. The evaluation and coevaluation of the mapped pairing are
F of those of the original pairing, conjugated by the tensorator and unit comparison.
Naturality, associativity and unit laws of the monoidal functor move these comparisons
past evaluation and coevaluation. The evaluation-coevaluation triangle identity then
cancels the inserted dual pair. What remains is the inverse tensorator followed by
F(K) tensor the counit, which is the claimed canonical transpose. This calculation
uses neither geometric hypotheses nor any invertibility of the counit. -/
theorem monoidal_projection_conjugate
    {C : Type u₁} {D : Type u₂} [Category.{v₁} C] [Category.{v₂} D]
    [MonoidalCategory C] [MonoidalCategory D]
    (F : C ⥤ D) (R : D ⥤ C) [F.Monoidal] (a : F ⊣ R)
    (K L : C) [ExactPairing K L] (E : D) :
    (@conjugateEquiv _ _ _ _ _ _ _ _
      ((tensorLeftAdjunction K L).comp a)
      (a.comp (@tensorLeftAdjunction D _ _ (F.obj K) (F.obj L)
        (ExactPairing.map F K L)))
      (Functor.Monoidal.commTensorLeft F L).hom).app E =
        (a.homEquiv _ _)
          ((Functor.Monoidal.μIso F K (R.obj E)).inv ≫
            F.obj K ◁ a.counit.app E) := by
  have pairing_map (A B : C) (q : A ⟶ K ⊗ B) :
      let p := ExactPairing.map F K L
      (@tensorLeftHomEquiv _ _ _ (F.obj A) (F.obj K) (F.obj L) (F.obj B) p).symm
        (F.map q ≫ δ F K B) =
          μ F L A ≫ F.map ((tensorLeftHomEquiv A K L B).symm q) := by
    let := ExactPairing.map F K L
    simp only [tensorLeftHomEquiv, Equiv.coe_fn_symm_mk]
    change F.obj L ◁ (F.map q ≫ δ F K B) ≫ _ = _
    simp only [Functor.map_comp, Functor.Monoidal.map_whiskerLeft,
      Functor.Monoidal.map_associator_inv, Functor.Monoidal.map_whiskerRight,
      whiskerLeft_comp, Category.assoc, Functor.Monoidal.μ_δ_assoc]
    change F.obj L ◁ F.map q ≫ F.obj L ◁ δ F K B ≫
      (α_ (F.obj L) (F.obj K) (F.obj B)).inv ≫
      (μ F L K ≫ F.map (ε_ K L) ≫ η F) ▷ F.obj B ≫ (λ_ (F.obj B)).hom = _
    simp only [comp_whiskerRight, Category.assoc]
    rw [Functor.Monoidal.map_leftUnitor]
    simp
  let := ExactPairing.map F K L
  let b₁ := (tensorLeftAdjunction K L).comp a
  let b₂ := a.comp (tensorLeftAdjunction (F.obj K) (F.obj L))
  apply (b₂.homEquiv _ E).symm.injective
  rw [Adjunction.homEquiv_counit]
  rw [conjugateEquiv_counit]
  dsimp only [b₁, b₂]
  simp only [Adjunction.comp_counit_app,
    Functor.Monoidal.commTensorLeft_hom_app, Functor.comp_obj]
  rw [Adjunction.comp_homEquiv]
  simp only [Equiv.symm_trans, Equiv.trans_apply]
  rw [← Adjunction.homEquiv_counit]
  change μ F L (K ⊗ R.obj E) ≫
    (a.homEquiv (L ⊗ (K ⊗ R.obj E)) E).symm
      ((tensorLeftAdjunction K L).counit.app (R.obj E)) =
    ((tensorLeftAdjunction (F.obj K) (F.obj L)).homEquiv _ E).symm
      ((a.homEquiv (K ⊗ R.obj E) (F.obj K ⊗ E)).symm
        ((a.homEquiv (K ⊗ R.obj E) (F.obj K ⊗ E)) _))
  rw [Equiv.symm_apply_apply]
  simp only [tensorLeftAdjunction, Adjunction.mkOfHomEquiv_homEquiv]
  have hn := (tensorLeftAdjunction (F.obj K) (F.obj L)).homEquiv_naturality_right_symm
    ((Functor.Monoidal.μIso F K (R.obj E)).inv) (a.counit.app E)
  simp only [tensorLeftAdjunction, Adjunction.mkOfHomEquiv_homEquiv] at hn
  have hn' : (tensorLeftHomEquiv (F.obj (K ⊗ R.obj E)) (F.obj K) (F.obj L) E).symm
      ((Functor.Monoidal.μIso F K (R.obj E)).inv ≫ F.obj K ◁ a.counit.app E) =
    (tensorLeftHomEquiv (F.obj (K ⊗ R.obj E)) (F.obj K) (F.obj L)
      (F.obj (R.obj E))).symm (δ F K (R.obj E)) ≫ a.counit.app E := by
    convert hn using 1 <;> congr 3
  dsimp only [tensorLeft, curriedTensor]
  rw [hn']
  change _ = (tensorLeftHomEquiv (F.obj (K ⊗ R.obj E))
    (F.obj K) (F.obj L) (F.obj (R.obj E))).symm (δ F K (R.obj E)) ≫ _
  have hh := pairing_map (K ⊗ R.obj E) (R.obj E) (𝟙 _)
  simp only [Functor.map_id, Category.id_comp] at hh
  rw [hh]
  rw [Adjunction.homEquiv_counit]
  simp only [Category.assoc]
  rfl

end CategoryTheory
