/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.TopologicalInvariance
public import Mathlib.AlgebraicGeometry.Restrict
import WeilConjectures.AlgebraicGeometry.EtaleCohomologyPullbackFunctorial
import WeilConjectures.SixFunctors.BaseChange.Pasting
import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Coherence

/-! # Canonical cohomology cocone on inverse-image opens

Source: Stacks Project, Tags 09YQ and 01F7.
-/

@[expose] public section

universe u
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.Etale

set_option backward.isDefEq.respectTransparency false

/-- Restrict a coefficient map across a commuting square.
Source: Stacks Project, Tag 01F7, composition and coefficient naturality.
(blueprint: lem-weil-pbc-etale-limit-open-cohomology-cocone). -/
noncomputable def openSquareCoefficient
    {X Y X' Y' : Scheme.{u}} (f : Y ⟶ X) (a : X' ⟶ X) (b : Y' ⟶ Y)
    (g : Y' ⟶ X') (h : b ≫ f = g ≫ a)
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1})
    (G : Sheaf Y.smallEtaleTopology AddCommGrpCat.{u + 1})
    (φ : (upperStar AddCommGrpCat.{u + 1} f).obj F ⟶ G) :
    (upperStar AddCommGrpCat.{u + 1} g).obj
      ((upperStar AddCommGrpCat.{u + 1} a).obj F) ⟶
        (upperStar AddCommGrpCat.{u + 1} b).obj G :=
  (upperStarComp AddCommGrpCat.{u + 1} g a (b ≫ f) h).inv.app F ≫
    (upperStarComp AddCommGrpCat.{u + 1} b f).hom.app F ≫
      (upperStar AddCommGrpCat.{u + 1} b).map φ

private theorem pullback_comp_transport {A B C : Scheme.{u}}
    (a : A ⟶ B) (b : B ⟶ C) (k : A ⟶ C) (h : k = a ≫ b)
    (F : Sheaf C.smallEtaleTopology AddCommGrpCat.{u + 1}) (n : ℕ)
    (x : Sheaf.H F n) :
    Sheaf.H.map ((upperStarComp AddCommGrpCat.{u + 1} a b k h).hom.app F) n
      (cohomologyMap k F n x) = cohomologyMap a _ n (cohomologyMap b F n x) := by
  subst k
  exact ((cohomologyPullbackFunctorial a b F n).2.1 x).symm

set_option backward.isDefEq.respectTransparency false in
/-- Pullback on cohomology commutes with restriction across a commuting square.
Source: Stacks Project, Tag 01F7.
(blueprint: lem-weil-pbc-etale-limit-open-cohomology-cocone). -/
theorem openSquareCoefficient_cohomology
    {X Y X' Y' : Scheme.{u}} (f : Y ⟶ X) (a : X' ⟶ X) (b : Y' ⟶ Y)
    (g : Y' ⟶ X') (h : b ≫ f = g ≫ a)
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1})
    (G : Sheaf Y.smallEtaleTopology AddCommGrpCat.{u + 1})
    (φ : (upperStar AddCommGrpCat.{u + 1} f).obj F ⟶ G) (n : ℕ) :
    AddCommGrpCat.ofHom (cohomologyMap a F n) ≫
      AddCommGrpCat.ofHom
        (cohomologyMap g ((upperStar AddCommGrpCat.{u + 1} a).obj F) n) ≫
      AddCommGrpCat.ofHom (Sheaf.H.map (openSquareCoefficient f a b g h F G φ) n) =
    AddCommGrpCat.ofHom (cohomologyMap f F n) ≫
      AddCommGrpCat.ofHom (Sheaf.H.map φ n) ≫
      AddCommGrpCat.ofHom (cohomologyMap b G n) := by
  ext x
  change Sheaf.H.map (openSquareCoefficient f a b g h F G φ) n
    (cohomologyMap g _ n (cohomologyMap a F n x)) =
      cohomologyMap b G n (Sheaf.H.map φ n (cohomologyMap f F n x))
  have hs : Sheaf.H.map
      ((upperStarComp AddCommGrpCat.{u + 1} g a (b ≫ f) h).hom.app F) n
      (cohomologyMap (b ≫ f) F n x) =
        cohomologyMap g _ n (cohomologyMap a F n x) := by
    exact pullback_comp_transport g a (b ≫ f) h F n x
  rw [← hs]
  dsimp only [openSquareCoefficient]
  rw [Sheaf.H.map_comp_apply, Sheaf.H.map_comp_apply]
  have hi := Sheaf.H.map_comp_apply
    ((upperStarComp AddCommGrpCat.{u + 1} g a (b ≫ f) h).hom.app F)
    ((upperStarComp AddCommGrpCat.{u + 1} g a (b ≫ f) h).inv.app F)
    (cohomologyMap (b ≫ f) F n x)
  simp only [Iso.hom_inv_id_app, Sheaf.H.map_id_apply] at hi
  exact (congrArg (fun y ↦ Sheaf.H.map
    ((upperStar AddCommGrpCat.{u + 1} b).map φ) n
    (Sheaf.H.map ((upperStarComp AddCommGrpCat.{u + 1} b f).hom.app F) n y))
    hi.symm).trans
      ((congrArg (Sheaf.H.map ((upperStar AddCommGrpCat.{u + 1} b).map φ) n)
        ((cohomologyPullbackFunctorial b f F n).2.1 x).symm).trans
          (cohomologyMap_map b n φ (cohomologyMap f F n x)).symm)

/-- The open at a tail stage, pulled back from a morphism at the least index.
Source: Stacks Project, Tag 09YQ, inverse-image open system.
(blueprint: lem-weil-pbc-etale-limit-open-cohomology-cocone). -/
abbrev tailStageOpen {I : Type u} [Preorder I] (D : Iᵒᵖ ⥤ Scheme.{u})
    {X : Scheme.{u}} {i₀ : I} (g₀ : D.obj (op i₀) ⟶ X) (W : X.Opens)
    (j : Set.Ici i₀) : (D.obj (op j.val)).Opens :=
  (D.map (homOfLE j.property).op ≫ g₀) ⁻¹ᵁ W

/-- Transition between the inverse-image opens.
Source: Stacks Project, Tag 09YQ.
(blueprint: lem-weil-pbc-etale-limit-open-cohomology-cocone). -/
noncomputable def tailStageOpenMap {I : Type u} [Preorder I]
    (D : Iᵒᵖ ⥤ Scheme.{u}) {X : Scheme.{u}} {i₀ : I}
    (g₀ : D.obj (op i₀) ⟶ X) (W : X.Opens)
    {j k : Set.Ici i₀} (f : j ⟶ k) :
    (tailStageOpen D g₀ W k).toScheme ⟶ (tailStageOpen D g₀ W j).toScheme :=
  (D.map (homOfLE (show j.val ≤ k.val from f.le)).op).resLE _ _ (by
    dsimp only [tailStageOpen]
    rw [← Scheme.Hom.comp_preimage, ← Category.assoc, ← D.map_comp]
    rfl)

/-- Projection of the limit open to a tail-stage open.
Source: Stacks Project, Tag 09YQ.
(blueprint: lem-weil-pbc-etale-limit-open-cohomology-cocone). -/
noncomputable def tailLimitOpenMap {I : Type u} [Preorder I]
    (D : Iᵒᵖ ⥤ Scheme.{u}) (c : Cone D) {X : Scheme.{u}} {i₀ : I}
    (g₀ : D.obj (op i₀) ⟶ X) (W : X.Opens) (j : Set.Ici i₀) :
    ((c.π.app (op i₀) ≫ g₀) ⁻¹ᵁ W).toScheme ⟶
      (tailStageOpen D g₀ W j).toScheme :=
  (c.π.app (op j.val)).resLE _ _ (by
    dsimp only [tailStageOpen]
    rw [← Scheme.Hom.comp_preimage, ← Category.assoc, c.w])

/-- Canonical cohomology transition on the restricted stage opens.
Source: Stacks Project, Tags 09YQ and 01F7.
(blueprint: lem-weil-pbc-etale-limit-open-cohomology-cocone). -/
noncomputable def tailOpenCohomologyMap {I : Type u} [Preorder I]
    (D : Iᵒᵖ ⥤ Scheme.{u}) {X : Scheme.{u}} {i₀ : I}
    (g₀ : D.obj (op i₀) ⟶ X) (W : X.Opens)
    (F : ∀ i : I, Sheaf (D.obj (op i)).smallEtaleTopology AddCommGrpCat.{u + 1})
    (φ : ∀ {i j : I} (f : i ⟶ j),
      (upperStar AddCommGrpCat.{u + 1} (D.map f.op)).obj (F i) ⟶ F j)
    {j k : Set.Ici i₀} (f : j ⟶ k) :
    AddCommGrpCat.of (Sheaf.H
      ((upperStar AddCommGrpCat.{u + 1} (tailStageOpen D g₀ W j).ι).obj (F j.val)) 0) ⟶
    AddCommGrpCat.of (Sheaf.H
      ((upperStar AddCommGrpCat.{u + 1} (tailStageOpen D g₀ W k).ι).obj (F k.val)) 0) :=
  AddCommGrpCat.ofHom (cohomologyMap (tailStageOpenMap D g₀ W f) _ 0) ≫
    AddCommGrpCat.ofHom (Sheaf.H.map
      (openSquareCoefficient (D.map (homOfLE (show j.val ≤ k.val from f.le)).op)
        (tailStageOpen D g₀ W j).ι (tailStageOpen D g₀ W k).ι
        (tailStageOpenMap D g₀ W f)
        (by simp only [tailStageOpenMap, Scheme.Hom.resLE_comp_ι])
        (F j.val) (F k.val)
        (φ (homOfLE (show j.val ≤ k.val from f.le)))) 0)

/-- Canonical cohomology leg from a stage open to the limit open.
Source: Stacks Project, Tags 09YQ and 01F7.
(blueprint: lem-weil-pbc-etale-limit-open-cohomology-cocone). -/
noncomputable def tailOpenCohomologyLeg {I : Type u} [Preorder I]
    (D : Iᵒᵖ ⥤ Scheme.{u}) (c : Cone D) {X : Scheme.{u}} {i₀ : I}
    (g₀ : D.obj (op i₀) ⟶ X) (W : X.Opens)
    (F : ∀ i : I, Sheaf (D.obj (op i)).smallEtaleTopology AddCommGrpCat.{u + 1})
    (G : I ⥤ Sheaf c.pt.smallEtaleTopology AddCommGrpCat.{u + 1})
    (eG : ∀ i : I, G.obj i ≅
      (upperStar AddCommGrpCat.{u + 1} (c.π.app (op i))).obj (F i))
    (L : Cocone G) (j : Set.Ici i₀) :
    AddCommGrpCat.of (Sheaf.H
      ((upperStar AddCommGrpCat.{u + 1} (tailStageOpen D g₀ W j).ι).obj (F j.val)) 0) ⟶
    AddCommGrpCat.of (Sheaf.H
      ((upperStar AddCommGrpCat.{u + 1}
        ((c.π.app (op i₀) ≫ g₀) ⁻¹ᵁ W).ι).obj L.pt) 0) :=
  AddCommGrpCat.ofHom (cohomologyMap (tailLimitOpenMap D c g₀ W j) _ 0) ≫
    AddCommGrpCat.ofHom (Sheaf.H.map
      (openSquareCoefficient (c.π.app (op j.val)) (tailStageOpen D g₀ W j).ι
        ((c.π.app (op i₀) ≫ g₀) ⁻¹ᵁ W).ι (tailLimitOpenMap D c g₀ W j)
        (by simp only [tailLimitOpenMap, Scheme.Hom.resLE_comp_ι]) (F j.val) L.pt
        ((eG j.val).inv ≫ L.ι.app j.val)) 0)

-- The arguments below specialize the already proved square and arrow laws.
-- Their original modules import this module, so importing them here would cycle.
-- Sources: EtaleOpenSquareDiagramIdentity, TailOpenCohomologyArrowLaws,
-- and TailOpenCohomologyLegNaturality (Stacks Tags 09YQ, 01F7, 03CB).

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
private theorem openSquareCoefficient_diagram_identity
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

private theorem functor_transport_map
    {α C D : Type*} [Category C] [Category D]
    (P : α → C ⥤ D) (K : D ⥤ AddCommGrpCat.{u + 1}) (F : C) {A : Type*}
    (m : ∀ a, A → K.obj ((P a).obj F)) (a b : α) (h : a = b) (x : A) :
    K.map ((eqToIso (congrArg P h)).hom.app F) (m a x) = m b x := by
  subst b
  simp

set_option backward.isDefEq.respectTransparency false in
private theorem cohomology_identity_transport {X : Scheme.{u}} (f : X ⟶ X)
    (hf : f = 𝟙 X) (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1})
    (n : ℕ) (x : Sheaf.H F n) :
    Sheaf.H.map
      ((eqToIso (congrArg (upperStar AddCommGrpCat.{u + 1}) hf)).hom.app F ≫
        (upperStarId AddCommGrpCat.{u + 1} X).hom.app F) n
      (cohomologyMap f F n x) = x := by
  rw [Sheaf.H.map_comp_apply]
  have ht := functor_transport_map (upperStar AddCommGrpCat.{u + 1})
    (Sheaf.functorH X.smallEtaleTopology n) F
    (fun f x ↦ cohomologyMap f F n x) f (𝟙 X) hf x
  change Sheaf.H.map
    ((eqToIso (congrArg (upperStar AddCommGrpCat.{u + 1}) hf)).hom.app F) n
    (cohomologyMap f F n x) = cohomologyMap (𝟙 X) F n x at ht
  exact (congrArg (Sheaf.H.map ((upperStarId AddCommGrpCat.{u + 1} X).hom.app F) n)
    ht).trans ((cohomologyPullbackFunctorial (𝟙 X) (𝟙 X) F n).2.2 x)

set_option backward.isDefEq.respectTransparency false in
private theorem openSquareCoefficient_composition
    {X Y Z X' Y' Z' : Scheme.{u}}
    (f : Y ⟶ X) (k : Z ⟶ Y) (a : X' ⟶ X) (b : Y' ⟶ Y) (d : Z' ⟶ Z)
    (g : Y' ⟶ X') (l : Z' ⟶ Y')
    (h₁ : b ≫ f = g ≫ a) (h₂ : d ≫ k = l ≫ b)
    (q : Z ⟶ X) (r : Z' ⟶ X') (hq : q = k ≫ f) (hr : r = l ≫ g)
    (h : d ≫ q = r ≫ a)
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1})
    (G : Sheaf Y.smallEtaleTopology AddCommGrpCat.{u + 1})
    (H : Sheaf Z.smallEtaleTopology AddCommGrpCat.{u + 1})
    (φ : (upperStar AddCommGrpCat.{u + 1} f).obj F ⟶ G)
    (ψ : (upperStar AddCommGrpCat.{u + 1} k).obj G ⟶ H) :
    openSquareCoefficient q a d r h F H
      ((upperStarComp AddCommGrpCat.{u + 1} k f q hq).hom.app F ≫
        (upperStar AddCommGrpCat.{u + 1} k).map φ ≫ ψ) =
    (upperStarComp AddCommGrpCat.{u + 1} l g r hr).hom.app
        ((upperStar AddCommGrpCat.{u + 1} a).obj F) ≫
      (upperStar AddCommGrpCat.{u + 1} l).map
        (openSquareCoefficient f a b g h₁ F G φ) ≫
      openSquareCoefficient k b d l h₂ G H ψ := by
  cases hq
  cases hr
  have hp := congrArg (fun t ↦ t.app F)
    (squareUpperStarIso_paste_vert_hom AddCommGrpCat.{u + 1}
      (CommSq.mk h₂) (CommSq.mk h₁) (CommSq.mk h))
  simp only [Functor.whiskerLeft_app, Functor.whiskerRight_app,
    NatTrans.comp_app, TwoSquare.vComp_app, Functor.comp_obj] at hp
  change (squareUpperStarIso AddCommGrpCat.{u + 1} (CommSq.mk h)).hom.app F ≫
      (upperStar AddCommGrpCat.{u + 1} d).map
        ((upperStarComp AddCommGrpCat.{u + 1} k f).hom.app F ≫
          (upperStar AddCommGrpCat.{u + 1} k).map φ ≫ ψ) = _
  rw [hp]
  simp only [Functor.map_comp, Category.assoc]
  rw [← Functor.map_comp_assoc, Iso.inv_hom_id_app]
  simp only [Functor.comp_obj, CategoryTheory.Functor.map_id, Category.id_comp]
  unfold openSquareCoefficient
  change _ = (upperStarComp AddCommGrpCat.{u + 1} l g).hom.app _ ≫
    (upperStar AddCommGrpCat.{u + 1} l).map
      ((squareUpperStarIso AddCommGrpCat.{u + 1} (CommSq.mk h₁)).hom.app F ≫
        (upperStar AddCommGrpCat.{u + 1} b).map φ) ≫
      (squareUpperStarIso AddCommGrpCat.{u + 1} (CommSq.mk h₂)).hom.app G ≫
        (upperStar AddCommGrpCat.{u + 1} d).map ψ
  rw [Functor.map_comp]
  simp only [Category.assoc]
  have hn := (squareUpperStarIso AddCommGrpCat.{u + 1} (CommSq.mk h₂)).hom.naturality φ
  simp only [Functor.comp_map] at hn
  rw [reassoc_of% hn]

private theorem coefficientCohomology_composition {A B C : Scheme.{u}}
    (a : A ⟶ B) (b : B ⟶ C) (t : A ⟶ C) (h : t = a ≫ b)
    (F : Sheaf C.smallEtaleTopology AddCommGrpCat.{u + 1})
    (G : Sheaf B.smallEtaleTopology AddCommGrpCat.{u + 1})
    (H : Sheaf A.smallEtaleTopology AddCommGrpCat.{u + 1})
    (α : (upperStar AddCommGrpCat.{u + 1} b).obj F ⟶ G)
    (β : (upperStar AddCommGrpCat.{u + 1} a).obj G ⟶ H) (n : ℕ) (x : Sheaf.H F n) :
    Sheaf.H.map ((upperStarComp AddCommGrpCat.{u + 1} a b t h).hom.app F ≫
      (upperStar AddCommGrpCat.{u + 1} a).map α ≫ β) n (cohomologyMap t F n x) =
      Sheaf.H.map β n (cohomologyMap a G n (Sheaf.H.map α n (cohomologyMap b F n x))) := by
  rw [Sheaf.H.map_comp_apply, Sheaf.H.map_comp_apply]
  exact (congrArg (fun y ↦ Sheaf.H.map β n
    (Sheaf.H.map ((upperStar AddCommGrpCat.{u + 1} a).map α) n y))
    (pullback_comp_transport a b t h F n x)).trans
    (congrArg (Sheaf.H.map β n) (cohomologyMap_map a n α (cohomologyMap b F n x)).symm)

private theorem tailOpenCohomologyMap_laws
    {I : Type u} [Preorder I] [IsDirected I (· ≤ ·)] [Nonempty I]
    (D : Iᵒᵖ ⥤ Scheme.{u})
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
    {X : Scheme.{u}} (i₀ : I) (g₀ : D.obj (op i₀) ⟶ X) (W : X.Opens) :
    (∀ j : Set.Ici i₀, tailOpenCohomologyMap D g₀ W F φ (𝟙 j) = 𝟙 _) ∧
    (∀ (j k l : Set.Ici i₀) (f : j ⟶ k) (g : k ⟶ l),
      tailOpenCohomologyMap D g₀ W F φ (f ≫ g) =
        tailOpenCohomologyMap D g₀ W F φ f ≫
          tailOpenCohomologyMap D g₀ W F φ g) := by
  let E : (Set.Ici i₀)ᵒᵖ ⥤ Scheme.{u} :=
    { obj j := (tailStageOpen D g₀ W j.unop).toScheme
      map f := tailStageOpenMap D g₀ W f.unop
      map_id j := by
        apply (cancel_mono (tailStageOpen D g₀ W j.unop).ι).mp
        simp only [tailStageOpenMap, Scheme.Hom.resLE_comp_ι, Category.id_comp]
        have h : (homOfLE (show j.unop.val ≤ j.unop.val from le_rfl)).op =
            𝟙 (op j.unop.val) := Subsingleton.elim _ _
        rw [h, D.map_id, Category.comp_id]
      map_comp f g := by
        apply (cancel_mono (tailStageOpen D g₀ W _).ι).mp
        simp only [Category.assoc, tailStageOpenMap, Scheme.Hom.resLE_comp_ι]
        rw [← Category.assoc, Scheme.Hom.resLE_comp_ι, Category.assoc, ← D.map_comp]
        rfl }
  let F' := fun j : Set.Ici i₀ ↦
    (upperStar AddCommGrpCat.{u + 1} (tailStageOpen D g₀ W j).ι).obj (F j.val)
  let ψ : ∀ {j k : Set.Ici i₀} (f : j ⟶ k),
      (upperStar AddCommGrpCat.{u + 1} (E.map f.op)).obj (F' j) ⟶ F' k :=
    fun {j k} f ↦
      openSquareCoefficient (D.map (homOfLE (show j.val ≤ k.val from f.le)).op)
          (tailStageOpen D g₀ W j).ι (tailStageOpen D g₀ W k).ι
          (tailStageOpenMap D g₀ W f)
          (by simp only [tailStageOpenMap, Scheme.Hom.resLE_comp_ι])
          (F j.val) (F k.val) (φ (homOfLE (show j.val ≤ k.val from f.le)))
  have hid : ∀ j : Set.Ici i₀, ψ (𝟙 j) =
      (eqToIso (congrArg (upperStar AddCommGrpCat.{u + 1}) (E.map_id (op j)))).hom.app
        (F' j) ≫ (upperStarId AddCommGrpCat.{u + 1} (E.obj (op j))).hom.app (F' j) := by
    intro j
    exact openSquareCoefficient_diagram_identity D E
      Subtype.val (fun j ↦ (tailStageOpen D g₀ W j).ι) F φ hidentity
      (fun j ↦ by
        simp only [E, tailStageOpenMap, Scheme.Hom.resLE_comp_ι])
      F' (fun _ ↦ rfl) (fun j ↦ ψ (𝟙 j)) (fun _ ↦ HEq.rfl) j
  have hcomp : ∀ (j k l : Set.Ici i₀) (f : j ⟶ k) (g : k ⟶ l),
      ψ (f ≫ g) =
        (upperStarComp AddCommGrpCat.{u + 1} (E.map g.op) (E.map f.op)
          (E.map (f ≫ g).op) (E.map_comp g.op f.op)).hom.app (F' j) ≫
        (upperStar AddCommGrpCat.{u + 1} (E.map g.op)).map (ψ f) ≫ ψ g := by
    intro j k l f g
    dsimp only [ψ]
    rw [show homOfLE (show j.val ≤ l.val from (f ≫ g).le) =
      homOfLE (show j.val ≤ k.val from f.le) ≫
        homOfLE (show k.val ≤ l.val from g.le) from Subsingleton.elim _ _]
    simp only [hcomposition]
    exact openSquareCoefficient_composition _ _ _ _ _ _ _ _ _ _ _
      (D.map_comp _ _) (E.map_comp g.op f.op) _ _ _ _ _ _
  constructor
  · intro j
    ext x
    change Sheaf.H.map (ψ (𝟙 j)) 0 (cohomologyMap (E.map (𝟙 (op j))) (F' j) 0 x) = x
    rw [hid]
    exact cohomology_identity_transport _ (E.map_id (op j)) (F' j) 0 x
  · intro j k l f g
    ext x
    change Sheaf.H.map (ψ (f ≫ g)) 0
      (cohomologyMap (E.map (f ≫ g).op) (F' j) 0 x) =
        Sheaf.H.map (ψ g) 0 (cohomologyMap (E.map g.op) (F' k) 0
          (Sheaf.H.map (ψ f) 0 (cohomologyMap (E.map f.op) (F' j) 0 x)))
    rw [hcomp]
    exact coefficientCohomology_composition (E.map g.op) (E.map f.op)
      (E.map (f ≫ g).op) (E.map_comp g.op f.op) (F' j) (F' k) (F' l) (ψ f) (ψ g) 0 x

set_option backward.isDefEq.respectTransparency false in
/-- The restricted cohomology legs commute with the restricted transitions.
Source: Stacks Project, Tags 09YQ and 01F7.
(blueprint: lem-weil-pbc-tail-open-cohomology-leg-naturality).

Proof: Precompose the cocone equation G.map f; L_k = L_j by eG_j.inv and substitute hG.
Cancel the inverse isomorphisms to obtain the original coefficient leg equation.
Restrict it along the limit-open inclusion. The projection square and transition square
paste to the projection square at j. Vertical pasting of inverse-image square comparisons
and naturality in the coefficient transition identify the restricted coefficient equation
with the composite of the restricted transition and restricted leg at k. The scheme
projections compose because both agree after the stage-open inclusion, by c.w.
Apply cohomology pullback composition, coefficient naturality and Sheaf.H.map composition
to this coefficient equation. The displayed naturality equality follows. The argument
uses arbitrary cocones, and includes empty opens and zero coefficients. -/
private theorem tailOpenCohomologyLeg_naturality
    {I : Type u} [Preorder I] [IsDirected I (· ≤ ·)] [Nonempty I]
    (D : Iᵒᵖ ⥤ Scheme.{u}) (c : Cone D)
    (F : ∀ i : I, Sheaf (D.obj (op i)).smallEtaleTopology AddCommGrpCat.{u + 1})
    (φ : ∀ {i j : I} (f : i ⟶ j),
      (upperStar AddCommGrpCat.{u + 1} (D.map f.op)).obj (F i) ⟶ F j)
    (G : I ⥤ Sheaf c.pt.smallEtaleTopology AddCommGrpCat.{u + 1})
    (eG : ∀ i : I, G.obj i ≅
      (upperStar AddCommGrpCat.{u + 1} (c.π.app (op i))).obj (F i))
    (hG : ∀ (i j : I) (f : i ⟶ j), G.map f =
      (eG i).hom ≫
        (upperStarComp AddCommGrpCat.{u + 1} (c.π.app (op j)) (D.map f.op)
          (c.π.app (op i)) (c.w f.op).symm).hom.app (F i) ≫
        (upperStar AddCommGrpCat.{u + 1} (c.π.app (op j))).map (φ f) ≫ (eG j).inv)
    (L : Cocone G)
    {X : Scheme.{u}} (i₀ : I) (g₀ : D.obj (op i₀) ⟶ X) (W : X.Opens)
    (j k : Set.Ici i₀) (f : j ⟶ k) :
    tailOpenCohomologyMap D g₀ W F φ f ≫
      tailOpenCohomologyLeg D c g₀ W F G eG L k =
      tailOpenCohomologyLeg D c g₀ W F G eG L j := by
  let f₀ : j.val ⟶ k.val := homOfLE (show j.val ≤ k.val from f.le)
  have hr : tailLimitOpenMap D c g₀ W j =
      tailLimitOpenMap D c g₀ W k ≫ tailStageOpenMap D g₀ W f := by
    apply (cancel_mono (tailStageOpen D g₀ W j).ι).1
    rw [Category.assoc]
    simp only [tailStageOpenMap, Scheme.Hom.resLE_comp_ι]
    rw [← Category.assoc]
    simp only [tailLimitOpenMap, Scheme.Hom.resLE_comp_ι]
    exact congrArg (fun t => ((c.π.app (op i₀) ≫ g₀) ⁻¹ᵁ W).ι ≫ t)
      (c.w f₀.op).symm
  have h₁ : (tailStageOpen D g₀ W k).ι ≫ D.map f₀.op =
      tailStageOpenMap D g₀ W f ≫ (tailStageOpen D g₀ W j).ι := by
    simp only [tailStageOpenMap, Scheme.Hom.resLE_comp_ι]
    rfl
  have h₂ : ((c.π.app (op i₀) ≫ g₀) ⁻¹ᵁ W).ι ≫ c.π.app (op k.val) =
      tailLimitOpenMap D c g₀ W k ≫ (tailStageOpen D g₀ W k).ι := by
    simp only [tailLimitOpenMap, Scheme.Hom.resLE_comp_ι]
  have h₃ : ((c.π.app (op i₀) ≫ g₀) ⁻¹ᵁ W).ι ≫ c.π.app (op j.val) =
      tailLimitOpenMap D c g₀ W j ≫ (tailStageOpen D g₀ W j).ι := by
    simp only [tailLimitOpenMap, Scheme.Hom.resLE_comp_ι]
  have he : (upperStarComp AddCommGrpCat.{u + 1} (c.π.app (op k.val))
      (D.map f₀.op) (c.π.app (op j.val)) (c.w f₀.op).symm).hom.app (F j.val) ≫
      (upperStar AddCommGrpCat.{u + 1} (c.π.app (op k.val))).map (φ f₀) ≫
        ((eG k.val).inv ≫ L.ι.app k.val) = (eG j.val).inv ≫ L.ι.app j.val := by
    have hw := congrArg (fun t => (eG j.val).inv ≫ t) (L.w f₀)
    rw [hG] at hw
    simpa only [← Category.assoc, Iso.inv_hom_id, Category.id_comp] using hw
  have hp := openSquareCoefficient_composition (D.map f₀.op) (c.π.app (op k.val))
    (tailStageOpen D g₀ W j).ι (tailStageOpen D g₀ W k).ι
    ((c.π.app (op i₀) ≫ g₀) ⁻¹ᵁ W).ι
    (tailStageOpenMap D g₀ W f) (tailLimitOpenMap D c g₀ W k) h₁ h₂
    (c.π.app (op j.val)) (tailLimitOpenMap D c g₀ W j)
    (c.w f₀.op).symm hr h₃ (F j.val) (F k.val) L.pt (φ f₀)
    ((eG k.val).inv ≫ L.ι.app k.val)
  rw [he] at hp
  ext x
  change Sheaf.H.map _ 0 (cohomologyMap (tailLimitOpenMap D c g₀ W k) _ 0
    (Sheaf.H.map _ 0 (cohomologyMap (tailStageOpenMap D g₀ W f) _ 0 x))) = _
  rw [← coefficientCohomology_composition _ _ _ hr]
  rw [← hp]
  rfl

/-- The canonical restricted cohomology arrows and legs form a diagram and cocone.

Source: Stacks Project, Tag 09YQ (coherent systems) and Tag 01F7 (functoriality).
(blueprint: lem-weil-pbc-etale-limit-open-cohomology-cocone).

Proof: Use the displayed restricted cohomology groups as the objects of K and
`tailOpenCohomologyMap` as its arrows. The restricted scheme maps preserve
identities and reverse composition: cancel the monomorphic open inclusions and
use the functor laws of D. For coefficient identities, transport the original
identity equation along D.map_id and the restricted scheme identity. The left
and right unit laws of upperStarComp cancel the original unit comparison and
leave the restricted unit. Cohomology pullback along identity then gives map_id.
For composition, substitute hcomposition in the coefficient map. Vertical
pasting of squareUpperStarIso and naturality in the coefficient transition give
the restricted coefficient composition law. Pullback composition and coefficient
naturality convert it into map_comp for K.
For each j use `tailOpenCohomologyLeg` as the leg to the displayed limit-open
cohomology group. Precompose L.w by eG_j.inv and substitute hG; cancel eG_j to
obtain the original coefficient leg equation. The restricted projections compose
by c.w after cancellation of the open inclusion. Paste the transition square
with the projection square at k. The coefficient leg equation and square pasting
identify the resulting coefficient with the projection coefficient at j.
Cohomology composition and coefficient naturality give leg naturality. Assemble
these laws into the explicit functor K and natural transformation, and take all
eK to be identity isomorphisms. No choice of data from an existence theorem,
colimithood, geometric limit, compactness, affine transition, or continuity is
used. Empty opens, identity diagrams and zero coefficients obey the same laws. -/
theorem etale_limit_open_cohomology_cocone
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
    (L : Cocone G)
    {X : Scheme.{u}} (i₀ : I) (g₀ : D.obj (op i₀) ⟶ X) (W : X.Opens) :
    let BW := AddCommGrpCat.of (Sheaf.H
      ((upperStar AddCommGrpCat.{u + 1}
        ((c.π.app (op i₀) ≫ g₀) ⁻¹ᵁ W).ι).obj L.pt) 0)
    ∃ (K : Set.Ici i₀ ⥤ AddCommGrpCat.{u + 1})
      (eK : ∀ j : Set.Ici i₀, K.obj j ≅ AddCommGrpCat.of (Sheaf.H
        ((upperStar AddCommGrpCat.{u + 1} (tailStageOpen D g₀ W j).ι).obj (F j.val)) 0)),
      (∀ (j k : Set.Ici i₀) (f : j ⟶ k), K.map f =
        (eK j).hom ≫ tailOpenCohomologyMap D g₀ W F φ f ≫ (eK k).inv) ∧
      ∃ (ι : K ⟶ (Functor.const (Set.Ici i₀)).obj BW),
        ∀ j, ι.app j = (eK j).hom ≫ tailOpenCohomologyLeg D c g₀ W F G eG L j := by
  obtain ⟨hid, hcomp⟩ := tailOpenCohomologyMap_laws D F φ hidentity hcomposition
    i₀ g₀ W
  let K : Set.Ici i₀ ⥤ AddCommGrpCat.{u + 1} :=
    { obj := fun j ↦ AddCommGrpCat.of (Sheaf.H
        ((upperStar AddCommGrpCat.{u + 1} (tailStageOpen D g₀ W j).ι).obj (F j.val)) 0)
      map := fun f ↦ tailOpenCohomologyMap D g₀ W F φ f
      map_id := hid
      map_comp := fun f g ↦ hcomp _ _ _ f g }
  let ι : K ⟶ (Functor.const (Set.Ici i₀)).obj
      (AddCommGrpCat.of (Sheaf.H
        ((upperStar AddCommGrpCat.{u + 1}
          ((c.π.app (op i₀) ≫ g₀) ⁻¹ᵁ W).ι).obj L.pt) 0)) :=
    { app := fun j ↦ tailOpenCohomologyLeg D c g₀ W F G eG L j
      naturality := by
        intro j k f
        change tailOpenCohomologyMap D g₀ W F φ f ≫
          tailOpenCohomologyLeg D c g₀ W F G eG L k =
          tailOpenCohomologyLeg D c g₀ W F G eG L j ≫ 𝟙 _
        rw [Category.comp_id]
        exact tailOpenCohomologyLeg_naturality D c F φ G eG hG L i₀ g₀ W j k f }
  refine ⟨K, fun _ ↦ Iso.refl _, ?_, ι, ?_⟩
  · intro j k f
    exact (Category.id_comp _).symm.trans (congrArg (fun t ↦ 𝟙 _ ≫ t)
      (Category.comp_id _).symm)
  · intro j
    exact (Category.id_comp _).symm

end AlgebraicGeometry.Etale
