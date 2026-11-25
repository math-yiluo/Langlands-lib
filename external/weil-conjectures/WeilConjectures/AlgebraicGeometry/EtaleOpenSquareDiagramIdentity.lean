/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.EtaleLimitOpenCohomologyCocone
import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Coherence

/-! # Identity law for coefficient restriction between two diagrams

Source: Stacks Project, Tags 09YQ and 03CB.
(blueprint: lem-weil-pbc-open-square-diagram-identity).
-/

@[expose] public section

universe u
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.Etale

private theorem openSquareCoefficient_identity_normalized {X Y : Scheme.{u}}
    (a : Y ⟶ X) (k : Y ⟶ X) (hk : k = a)
    (h : k = 𝟙 Y ≫ a) (h' : k = a ≫ 𝟙 X)
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}) :
    (upperStarComp AddCommGrpCat.{u + 1} (𝟙 Y) a k h).inv.app F ≫
      (upperStarComp AddCommGrpCat.{u + 1} a (𝟙 X) k h').hom.app F ≫
        (upperStar AddCommGrpCat.{u + 1} a).map
          ((upperStarId AddCommGrpCat.{u + 1} X).hom.app F) =
      (upperStarId AddCommGrpCat.{u + 1} Y).hom.app
        ((upperStar AddCommGrpCat.{u + 1} a).obj F) := by
  subst k
  rw [upperStarComp_id_left, upperStarComp_id_right]
  simp only [Iso.trans_inv, Iso.trans_hom, Iso.symm_inv, Iso.symm_hom,
    Functor.isoWhiskerLeft_inv, Functor.isoWhiskerRight_hom, NatTrans.comp_app,
    Functor.whiskerLeft_app, Functor.whiskerRight_app, Functor.rightUnitor_hom_app,
    Functor.leftUnitor_inv_app, Functor.id_obj, Functor.comp_obj,
    Category.id_comp, ← CategoryTheory.Functor.map_comp, Iso.inv_hom_id_app,
    CategoryTheory.Functor.map_id,
    Category.comp_id]

private theorem dependent_app_heq {α : Type*} {β : α → Type*}
    (f : ∀ x, β x) {x y : α} (h : x = y) : HEq (f x) (f y) := by
  subst y
  rfl

private theorem eqToIso_comp_heq {C D : Type*} [Category C] [Category D]
    {L M : C ⥤ D} (e : L = M) (F : C) {Z : D} (f : M.obj F ⟶ Z) :
    HEq ((eqToIso e).hom.app F ≫ f) f := by
  cases e
  simp

private theorem square_identity_heq {X Y : Scheme.{u}}
    (a : Y ⟶ X) (f : X ⟶ X) (g : Y ⟶ Y)
    (hf : f = 𝟙 X) (hg : g = 𝟙 Y) (h : a ≫ f = g ≫ a)
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1})
    (φ : (upperStar AddCommGrpCat.{u + 1} f).obj F ⟶ F)
    (hφ : HEq φ ((upperStarId AddCommGrpCat.{u + 1} X).hom.app F)) :
    HEq (openSquareCoefficient f a a g h F F φ)
      ((upperStarId AddCommGrpCat.{u + 1} Y).hom.app
        ((upperStar AddCommGrpCat.{u + 1} a).obj F)) := by
  cases hf
  cases hg
  rw [eq_of_heq hφ]
  exact heq_of_eq
    (openSquareCoefficient_identity_normalized a (a ≫ 𝟙 X) (Category.comp_id a) h rfl F)

/-- Restricting an identity coefficient across the identity square gives the canonical unit.
Source: Stacks Project, Tag 09YQ (coherent coefficient systems), and sites.tex,
Tag 03CB (composition of inverse images), with the unit coherence of the chosen adjoints.
(blueprint: lem-weil-pbc-open-square-diagram-identity).

Proof: Fix j. Use hF' to identify the given restricted sheaf with a_j^*F_sigma(j)
and hψ to identify its coefficient map with the explicit square coefficient.
Substitute the original identity equation for the coefficient map.
The equality D.map_id identifies the underlying transition with the scheme identity;
E.map_id similarly identifies the restricted transition with its scheme identity.
Transport along these two equalities, retaining the eqToIso factors in the statement.
The square coefficient is now the inverse of the composition isomorphism for the
identity on E_j and a_j, followed by the composition isomorphism for a_j and the
identity on D_sigma(j), followed by a_j^* of the original unit. Apply the left unit
law upperStarComp_id_left and the right unit law upperStarComp_id_right. Their
components express the first factor as the restricted unit and the second as the
inverse of a_j^* of the original unit. Functoriality cancels the latter with the
last factor. The remaining map is the restricted unit, with the E.map_id transport
restored. No injectivity, directedness, scheme limit, or nonempty open is used;
the argument also covers zero coefficients and empty schemes. -/
theorem openSquareCoefficient_diagram_identity
    {I J : Type u} [Preorder I] [Preorder J]
    (D : Iᵒᵖ ⥤ Scheme.{u}) (E : Jᵒᵖ ⥤ Scheme.{u}) (σ : J → I)
    (a : ∀ j, E.obj (op j) ⟶ D.obj (op (σ j)))
    (F : ∀ i : I, Sheaf (D.obj (op i)).smallEtaleTopology AddCommGrpCat.{u + 1})
    (φ : ∀ {i j : I} (f : i ⟶ j),
      (upperStar AddCommGrpCat.{u + 1} (D.map f.op)).obj (F i) ⟶ F j)
    (hidentity : ∀ i : I, φ (𝟙 i) =
      (eqToIso (congrArg (upperStar AddCommGrpCat.{u + 1}) (D.map_id (op i)))).hom.app
        (F i) ≫ (upperStarId AddCommGrpCat.{u + 1} (D.obj (op i))).hom.app (F i))
    (h : ∀ j, a j ≫ D.map (homOfLE (le_refl (σ j))).op =
      E.map (homOfLE (le_refl j)).op ≫ a j)
    (F' : ∀ j, Sheaf (E.obj (op j)).smallEtaleTopology AddCommGrpCat.{u + 1})
    (hF' : ∀ j, F' j = (upperStar AddCommGrpCat.{u + 1} (a j)).obj (F (σ j)))
    (ψ : ∀ j, (upperStar AddCommGrpCat.{u + 1}
      (E.map (homOfLE (le_refl j)).op)).obj (F' j) ⟶ F' j)
    (hψ : ∀ j, HEq (ψ j)
      (openSquareCoefficient (D.map (homOfLE (le_refl (σ j))).op) (a j) (a j)
        (E.map (homOfLE (le_refl j)).op) (h j) (F (σ j)) (F (σ j))
        (φ (homOfLE (le_refl (σ j))))))
    (j : J) :
    ψ j =
      (eqToIso (congrArg (upperStar AddCommGrpCat.{u + 1}) (E.map_id (op j)))).hom.app
        (F' j) ≫ (upperStarId AddCommGrpCat.{u + 1} (E.obj (op j))).hom.app (F' j) := by
  have hid : homOfLE (le_refl (σ j)) = 𝟙 (σ j) := Subsingleton.elim _ _
  have hid' : homOfLE (le_refl j) = 𝟙 j := Subsingleton.elim _ _
  have hf : D.map (homOfLE (le_refl (σ j))).op = 𝟙 (D.obj (op (σ j))) := by
    simpa only [hid, op_id] using D.map_id (op (σ j))
  have hg : E.map (homOfLE (le_refl j)).op = 𝟙 (E.obj (op j)) := by
    simpa only [hid', op_id] using E.map_id (op j)
  have hφ := (dependent_app_heq (fun q : σ j ⟶ σ j ↦ φ q) hid).trans
    ((heq_of_eq (hidentity (σ j))).trans
      (eqToIso_comp_heq _ (F (σ j))
        ((upperStarId AddCommGrpCat.{u + 1} (D.obj (op (σ j)))).hom.app (F (σ j)))))
  have hc := square_identity_heq (a j) _ _ hf hg (h j) (F (σ j))
    (φ (homOfLE (le_refl (σ j)))) hφ
  have hu := eqToIso_comp_heq
    (congrArg (upperStar AddCommGrpCat.{u + 1}) (E.map_id (op j)))
    ((upperStar AddCommGrpCat.{u + 1} (a j)).obj (F (σ j)))
    ((upperStarId AddCommGrpCat.{u + 1} (E.obj (op j))).hom.app
      ((upperStar AddCommGrpCat.{u + 1} (a j)).obj (F (σ j))))
  have ht := dependent_app_heq
    (fun G : Sheaf (E.obj (op j)).smallEtaleTopology AddCommGrpCat.{u + 1} ↦
      (eqToIso (congrArg (upperStar AddCommGrpCat.{u + 1}) (E.map_id (op j)))).hom.app
        G ≫ (upperStarId AddCommGrpCat.{u + 1} (E.obj (op j))).hom.app G)
    (hF' j).symm
  exact eq_of_heq ((hψ j).trans (hc.trans (hu.symm.trans ht)))

end AlgebraicGeometry.Etale
