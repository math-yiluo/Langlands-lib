/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module
public import WeilConjectures.AlgebraicGeometry.EtaleCoefficientProductTransitions
import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Coherence

/-! # Compatibility of the canonical outgoing-arrow product embeddings

Source: Stacks Project, Tag 0EXZ, the adjoint components of γ.
-/

@[expose] public section
universe u
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.Etale

/-- The map to the outgoing-arrow product whose components are adjoint to the coefficient
transitions followed by the canonical injective embeddings. This is an explicit product lift.
Source: Stacks Project, Tag 0EXZ, definition of γ.
(blueprint: lem-weil-pbc-etale-coefficient-product-embedding-compatibility). -/
noncomputable def etaleCoefficientProductEmbedding
    {I : Type u} [Preorder I] (D : Iᵒᵖ ⥤ Scheme.{u})
    (F : ∀ i : I, Sheaf (D.obj (op i)).smallEtaleTopology AddCommGrpCat.{u + 1})
    (φ : ∀ {i j : I} (f : i ⟶ j),
      (upperStar AddCommGrpCat.{u + 1} (D.map f.op)).obj (F i) ⟶ F j)
    (i : I) : F i ⟶ etaleCoefficientInjectiveTarget D F i :=
  Pi.lift fun t : Σ k : I, i ⟶ k ↦
    (upperStarLowerStarAdjunction AddCommGrpCat.{u + 1} (D.map t.2.op)).homEquiv _ _
      (φ t.2 ≫ Injective.ι (F t.1))

private theorem adjointComp
    {R S T : Scheme.{u}} (f : S ⟶ R) (g : T ⟶ S) (h : T ⟶ R) (hh : h = g ≫ f)
    (X : Sheaf R.smallEtaleTopology AddCommGrpCat.{u + 1})
    (Y : Sheaf S.smallEtaleTopology AddCommGrpCat.{u + 1})
    (Z : Sheaf T.smallEtaleTopology AddCommGrpCat.{u + 1})
    (a : (upperStar AddCommGrpCat.{u + 1} f).obj X ⟶ Y)
    (b : (upperStar AddCommGrpCat.{u + 1} g).obj Y ⟶ Z) :
    (upperStarLowerStarAdjunction AddCommGrpCat.{u + 1} h).homEquiv X Z
      ((upperStarComp AddCommGrpCat.{u + 1} g f h hh).hom.app X ≫
        (upperStar AddCommGrpCat.{u + 1} g).map a ≫ b) ≫
          (lowerStarComp AddCommGrpCat.{u + 1} g f h hh).inv.app Z =
    (upperStarLowerStarAdjunction AddCommGrpCat.{u + 1} f).homEquiv X Y a ≫
      (lowerStar AddCommGrpCat.{u + 1} f).map
        ((upperStarLowerStarAdjunction AddCommGrpCat.{u + 1} g).homEquiv Y Z b) := by
  simp only [Adjunction.homEquiv_unit, Functor.map_comp]
  rw [← Category.assoc, ← Category.assoc, ← Category.assoc,
    upperStarComp_hom_app_unit_app AddCommGrpCat.{u + 1} g f X h hh]
  simp only [Category.assoc]
  rw [← (lowerStarComp AddCommGrpCat.{u + 1} g f h hh).hom.naturality_assoc
      ((upperStar AddCommGrpCat.{u + 1} g).map a),
    ← (lowerStarComp AddCommGrpCat.{u + 1} g f h hh).hom.naturality_assoc b]
  simp only [Iso.hom_inv_id_app, Category.comp_id, Adjunction.comp_unit_app,
    Functor.comp_map, Functor.comp_obj]
  simp only [Category.assoc]
  rw [← Functor.map_comp_assoc]
  have hn := (upperStarLowerStarAdjunction AddCommGrpCat.{u + 1} g).unit.naturality a
  dsimp only [Functor.id_map, Functor.comp_map] at hn
  rw [← hn]
  simp only [Functor.map_comp, Category.assoc]


/-- The canonical product embedding intertwines the coefficient and product transitions.
Source: Stacks Project, Tag 0EXZ, the assertion that γ is a map of systems.
(blueprint: lem-weil-pbc-etale-coefficient-product-embedding-compatibility).

Proof: fix f : i → j and project the desired square to the factor indexed by
 g : j → k. On the left the component is φ_f followed by the adjoint transpose of
φ_g followed by Injective.ι. On the right, naturality of homEquiv moves the embedding
of F_i inside the transpose defining ψ_f. The product-lift projection equation then
selects the component indexed by f followed by g, namely the transpose of
φ_(f≫g) followed by Injective.ι, followed by the inverse lowerStarComp comparison.
Use hcomposition to replace φ_(f≫g) by upperStarComp followed by the inverse image
of φ_f and by φ_g. The mate equation for upperStarComp and lowerStarComp, together
with naturality of the adjunction, identifies this transpose with the left component.
Since these component equations hold for every outgoing g, product extensionality
proves the square. No identity law, directedness, nonemptiness, or monicity is used. -/
theorem etale_coefficient_product_embedding_compatibility
    {I : Type u} [Preorder I] (D : Iᵒᵖ ⥤ Scheme.{u})
    (F : ∀ i : I, Sheaf (D.obj (op i)).smallEtaleTopology AddCommGrpCat.{u + 1})
    (φ : ∀ {i j : I} (f : i ⟶ j),
      (upperStar AddCommGrpCat.{u + 1} (D.map f.op)).obj (F i) ⟶ F j)
    (hcomposition : ∀ (i j k : I) (f : i ⟶ j) (g : j ⟶ k),
      φ (f ≫ g) =
        (upperStarComp AddCommGrpCat.{u + 1} (D.map g.op) (D.map f.op)
          (D.map (f ≫ g).op) (D.map_comp g.op f.op)).hom.app (F i) ≫
        (upperStar AddCommGrpCat.{u + 1} (D.map g.op)).map (φ f) ≫ φ g)
    (i j : I) (f : i ⟶ j) :
    φ f ≫ etaleCoefficientProductEmbedding D F φ j =
      (upperStar AddCommGrpCat.{u + 1} (D.map f.op)).map
        (etaleCoefficientProductEmbedding D F φ i) ≫ etaleCoefficientProductTransition D F f
    := by
  apply Pi.hom_ext
  intro t
  change (φ f ≫ etaleCoefficientProductEmbedding D F φ j) ≫ Pi.π _ t = _
  unfold etaleCoefficientProductEmbedding
  rw [Category.assoc, Pi.lift_comp_π]
  unfold etaleCoefficientProductTransition
  rw [Category.assoc, Pi.lift_comp_π,
    ← Adjunction.homEquiv_naturality_left_symm]
  apply ((upperStarLowerStarAdjunction AddCommGrpCat.{u + 1}
    (D.map f.op)).homEquiv _ _).injective
  rw [Equiv.apply_symm_apply, Adjunction.homEquiv_naturality_right]
  erw [Pi.lift_comp_π_assoc]
  dsimp only
  rw [hcomposition]
  simp only [Category.assoc]
  exact (adjointComp (D.map f.op) (D.map t.2.op) (D.map (f ≫ t.2).op)
    (D.map_comp t.2.op f.op) (F i) (F j) (Injective.under (F t.1))
    (φ f) (φ t.2 ≫ Injective.ι (F t.1))).symm

end AlgebraicGeometry.Etale
