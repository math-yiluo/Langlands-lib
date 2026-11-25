/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.EtaleLimitOpenRestrictedSystem
import Mathlib.CategoryTheory.Filtered.Final
import Mathlib.CategoryTheory.Adjunction.Limits

/-! # Restricting a coherent sheaf system and its colimit to tail opens

Source: Stacks Project, Tag 09YQ, coherent systems and their colimits.
-/

@[expose] public section

universe u
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.Etale

set_option backward.isDefEq.respectTransparency true in
/-- Coherent coefficients and their colimit restrict to the explicit tail opens.

Source: Stacks Project, Tag 09YQ (theorem-colimit), coherent-system construction;
Tag 01F7, functoriality of inverse image.
(blueprint: lem-weil-pbc-etale-limit-tail-open-coefficients).

Proof: Use the explicitly constructed restricted sheaves, coefficient maps and
limit isomorphisms from tailOpenRestrictedSystem_coherence. Its first three
clauses give the identity, composition and diagram-map equations. The tail
inclusion is final: directedness supplies an upper bound of any index and i₀,
and filteredness joins any two choices. Thus whiskering L with the inclusion
preserves its colimit. Inverse image is a left adjoint and preserves that
colimit. For the coefficient legs expand the inverse of tailOpenLimitIso;
the inverse-of-composite formula and functoriality of inverse image give exactly
openSquareCoefficient of the original coefficient leg. The construction also
works for empty opens, zero coefficients and a singleton diagram; it asserts
no geometric limit or cohomology continuity. -/
theorem etale_limit_tail_open_coefficients
    {I : Type u} [Preorder I] [IsDirected I (· ≤ ·)] [Nonempty I]
    (D : Iᵒᵖ ⥤ Scheme.{u}) (c : Cone D)
    (F : ∀ i : I, Sheaf (D.obj (op i)).smallEtaleTopology AddCommGrpCat.{u + 1})
    (φ : ∀ {i j : I} (f : i ⟶ j),
      (upperStar AddCommGrpCat.{u + 1} (D.map f.op)).obj (F i) ⟶ F j)
    (hidentity : ∀ i : I, φ (𝟙 i) =
      (eqToIso (congrArg (upperStar AddCommGrpCat.{u + 1}) (D.map_id (op i)))).hom.app
        (F i) ≫ (upperStarId AddCommGrpCat.{u + 1} (D.obj (op i))).hom.app (F i))
    (hcomposition : ∀ (i j k : I) (f : i ⟶ j) (g : j ⟶ k),
      φ (f ≫ g) =
        (upperStarComp AddCommGrpCat.{u + 1} (D.map g.op) (D.map f.op)
          (D.map (f ≫ g).op) (D.map_comp g.op f.op)).hom.app (F i) ≫
        (upperStar AddCommGrpCat.{u + 1} (D.map g.op)).map (φ f) ≫ φ g)
    (G : I ⥤ Sheaf c.pt.smallEtaleTopology AddCommGrpCat.{u + 1})
    (eG : ∀ i : I, G.obj i ≅
      (upperStar AddCommGrpCat.{u + 1} (c.π.app (op i))).obj (F i))
    (hG : ∀ (i j : I) (f : i ⟶ j), G.map f =
      (eG i).hom ≫
        (upperStarComp AddCommGrpCat.{u + 1} (c.π.app (op j)) (D.map f.op)
          (c.π.app (op i)) (c.w f.op).symm).hom.app (F i) ≫
        (upperStar AddCommGrpCat.{u + 1} (c.π.app (op j))).map (φ f) ≫ (eG j).inv)
    (L : Cocone G) (hL : IsColimit L)
    {X : Scheme.{u}} (i₀ : I) (g₀ : D.obj (op i₀) ⟶ X) (W : X.Opens) :
    let DW := tailOpenDiagram D g₀ W
    let cW := tailOpenCone D c g₀ W
    let FW := tailOpenSheaf D g₀ W F
    let φW := @tailOpenCoefficient _ _ D _ _ g₀ W F φ
    let R := upperStar AddCommGrpCat.{u + 1} ((c.π.app (op i₀) ≫ g₀) ⁻¹ᵁ W).ι
    let J := tailOpenInclusion i₀
    let GW := (J ⋙ G) ⋙ R
    let LW := R.mapCocone (L.whisker J)
    (∀ j, φW (𝟙 j) =
      (eqToIso (congrArg (upperStar AddCommGrpCat.{u + 1}) (DW.map_id (op j)))).hom.app
        (FW j) ≫ (upperStarId AddCommGrpCat.{u + 1} (DW.obj (op j))).hom.app (FW j)) ∧
    (∀ (j k l : Set.Ici i₀) (f : j ⟶ k) (g : k ⟶ l), φW (f ≫ g) =
      (upperStarComp AddCommGrpCat.{u + 1} (DW.map g.op) (DW.map f.op)
        (DW.map (f ≫ g).op) (DW.map_comp g.op f.op)).hom.app (FW j) ≫
      (upperStar AddCommGrpCat.{u + 1} (DW.map g.op)).map (φW f) ≫ φW g) ∧
    (let eGW := tailOpenLimitIso D c g₀ W F G eG;
      (∀ (j k : Set.Ici i₀) (f : j ⟶ k), GW.map f =
        (eGW j).hom ≫
          (upperStarComp AddCommGrpCat.{u + 1} (cW.π.app (op k)) (DW.map f.op)
            (cW.π.app (op j)) (cW.w f.op).symm).hom.app (FW j) ≫
          (upperStar AddCommGrpCat.{u + 1} (cW.π.app (op k))).map (φW f) ≫
            (eGW k).inv) ∧
      Nonempty (IsColimit LW) ∧
      (∀ j : Set.Ici i₀, (eGW j).inv ≫ LW.ι.app j =
        openSquareCoefficient (c.π.app (op j.val)) (tailStageOpen D g₀ W j).ι
          ((c.π.app (op i₀) ≫ g₀) ⁻¹ᵁ W).ι (tailLimitOpenMap D c g₀ W j)
          (by simp only [tailLimitOpenMap, Scheme.Hom.resLE_comp_ι]) (F j.val) L.pt
          ((eG j.val).inv ≫ L.ι.app j.val))) := by
  let : Nonempty (Set.Ici i₀) := ⟨⟨i₀, le_rfl⟩⟩
  let : IsDirected (Set.Ici i₀) (· ≤ ·) := ⟨fun j k ↦ by
    obtain ⟨l, hj, hk⟩ := exists_ge_ge j.val k.val
    exact ⟨⟨l, j.property.trans hj⟩, hj, hk⟩⟩
  obtain ⟨hid, hcomp, hmap, _⟩ :=
    tailOpenRestrictedSystem_coherence D c F φ hidentity hcomposition G eG hG i₀ g₀ W
  let J := tailOpenInclusion i₀
  let : J.Final := by
    apply Functor.final_of_exists_of_isFiltered J
    · intro i
      obtain ⟨k, hik, h₀k⟩ := exists_ge_ge i i₀
      exact ⟨⟨k, h₀k⟩, ⟨homOfLE hik⟩⟩
    · intro i j f g
      exact ⟨j, 𝟙 j, Subsingleton.elim _ _⟩
  refine ⟨hid, hcomp, hmap, ?_, ?_⟩
  · exact ⟨isColimitOfPreserves _
      ((Functor.Final.isColimitWhiskerEquiv J L).symm hL)⟩
  · intro j
    simp only [tailOpenLimitIso, Functor.mapCocone_ι_app, Cocone.whisker,
      Functor.whiskerLeft_app, tailOpenInclusion, openSquareCoefficient,
      Iso.trans_inv, Iso.symm_inv, Iso.app_inv, Functor.mapIso_inv,
      Functor.map_comp, Category.assoc]

end AlgebraicGeometry.Etale
