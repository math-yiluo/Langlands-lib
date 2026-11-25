/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module
public import WeilConjectures.AlgebraicGeometry.EtaleCoefficientInjectiveSystemData

/-! # Identity calculation at one outgoing-arrow factor

Source: Stacks Project, Tag 0EXZ, canonical product components.
-/

@[expose] public section
universe u
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.Etale

private theorem identity_component
    {V W : Scheme.{u}} (f : V ⟶ V) (hf : f = 𝟙 V) (g : W ⟶ V)
    (hgf : g = g ≫ f)
    (J : Sheaf W.smallEtaleTopology AddCommGrpCat.{u + 1})
    (P : Sheaf V.smallEtaleTopology AddCommGrpCat.{u + 1})
    (p : P ⟶ (lowerStar AddCommGrpCat.{u + 1} g).obj J) :
    ((upperStarLowerStarAdjunction AddCommGrpCat.{u + 1} f).homEquiv _ _).symm
        (p ≫ (lowerStarComp AddCommGrpCat.{u + 1} g f g hgf).inv.app J) =
      ((eqToIso (congrArg (upperStar AddCommGrpCat.{u + 1}) hf)).hom.app P ≫
        (upperStarId AddCommGrpCat.{u + 1} V).hom.app P) ≫ p := by
  cases hf
  simp only [eqToIso_refl, Iso.refl_hom, NatTrans.id_app, Category.id_comp]
  rw [lowerStarComp_id_right]
  apply ((upperStarLowerStarAdjunction AddCommGrpCat.{u + 1} (𝟙 V)).homEquiv _ _).injective
  simp only [Equiv.apply_symm_apply]
  rw [Adjunction.homEquiv_naturality_right, Adjunction.homEquiv_unit]
  rw [upperStarId_hom_app_unit_app]
  simpa only [Iso.trans_inv, NatTrans.comp_app, Functor.rightUnitor_inv_app,
    Functor.isoWhiskerLeft_inv, Functor.whiskerLeft_app, Category.id_comp,
    Functor.id_map] using (lowerStarId AddCommGrpCat.{u + 1} V).inv.naturality p

/-- Identity calculation at one outgoing-arrow factor.
Source: Stacks Project, Tag 0EXZ, canonical maps ψ, expanded with the adjunction
mate equations and direct-image coherence in UpperLowerStar.Coherence.
(blueprint: lem-weil-pbc-etale-coefficient-product-identity-component).

Proof: replace id composed with the outgoing arrow by that arrow. Transport the
scheme morphism D(id) to the identity via D.map_id. The inverse right unit equation
for lowerStarComp identifies the direct-image comparison with lowerStarId.inv at
this factor. Apply the injective adjunction homEquiv to both sides. Its naturality
in the target makes the transpose of the proposed identity component equal to the
transpose of upperStarId.hom followed by the direct image of the projection. The
unit mate equation upperStarId_hom_app_unit_app identifies that transpose with
lowerStarId.inv at the product. Naturality of lowerStarId.inv moves the projection
past this identity comparison and gives the left side. This is a single-factor
calculation; no product extensionality or composition law is asserted. -/
theorem etale_coefficient_product_identity_component
    {I : Type u} [Preorder I] (D : Iᵒᵖ ⥤ Scheme.{u})
    (F : ∀ i : I, Sheaf (D.obj (op i)).smallEtaleTopology AddCommGrpCat.{u + 1}) (i : I)
    (t : Σ l : I, i ⟶ l) :
    ((upperStarLowerStarAdjunction AddCommGrpCat.{u + 1} (D.map (𝟙 i).op)).homEquiv _ _).symm
      (Pi.π (fun t : Σ l : I, i ⟶ l ↦
          (lowerStar AddCommGrpCat.{u + 1} (D.map t.2.op)).obj
            (Injective.under (F t.1))) ⟨t.1, (𝟙 i) ≫ t.2⟩ ≫
        (lowerStarComp AddCommGrpCat.{u + 1} (D.map t.2.op) (D.map (𝟙 i).op)
          (D.map ((𝟙 i) ≫ t.2).op) (D.map_comp t.2.op (𝟙 i).op)).inv.app
            (Injective.under (F t.1))) =
      ((eqToIso (congrArg (upperStar AddCommGrpCat.{u + 1}) (D.map_id (op i)))).hom.app
        (etaleCoefficientInjectiveTarget D F i) ≫
      (upperStarId AddCommGrpCat.{u + 1} (D.obj (op i))).hom.app
        (etaleCoefficientInjectiveTarget D F i)) ≫ Pi.π (fun t : Σ l : I, i ⟶ l ↦
          (lowerStar AddCommGrpCat.{u + 1} (D.map t.2.op)).obj
            (Injective.under (F t.1))) t := by
  have h := identity_component (D.map (𝟙 i).op) (D.map_id (op i)) (D.map t.2.op)
    (D.map_comp t.2.op (𝟙 i).op) (Injective.under (F t.1))
    _ (Pi.π (fun t : Σ l : I, i ⟶ l ↦
      (lowerStar AddCommGrpCat.{u + 1} (D.map t.2.op)).obj
        (Injective.under (F t.1))) t)
  convert h using 1
  congr! 3

end AlgebraicGeometry.Etale
