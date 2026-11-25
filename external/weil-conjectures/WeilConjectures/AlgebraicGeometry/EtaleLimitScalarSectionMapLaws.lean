/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.TopologicalInvariance

/-! # Scalar section comparison along an inverse system
Source: Stacks Project, Tags 09YN and 09YQ.
-/

@[expose] public section
universe u
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.Etale

-- Transposing a composite inverse-image map gives the composite transposes.
private theorem transpose_comp
    {R S T : Scheme.{u}} (p : T ⟶ S) (q : S ⟶ R) (r : T ⟶ R)
    (hr : r = p ≫ q)
    (F₀ : Sheaf R.smallEtaleTopology AddCommGrpCat.{u + 1})
    (F₁ : Sheaf S.smallEtaleTopology AddCommGrpCat.{u + 1})
    (F₂ : Sheaf T.smallEtaleTopology AddCommGrpCat.{u + 1})
    (α : (upperStar AddCommGrpCat.{u + 1} q).obj F₀ ⟶ F₁)
    (β : (upperStar AddCommGrpCat.{u + 1} p).obj F₁ ⟶ F₂) :
    (upperStarLowerStarAdjunction AddCommGrpCat.{u + 1} r).unit.app F₀ ≫
        (lowerStar AddCommGrpCat.{u + 1} r).map
          ((upperStarComp AddCommGrpCat.{u + 1} p q r hr).hom.app F₀ ≫
            (upperStar AddCommGrpCat.{u + 1} p).map α ≫ β) =
      (upperStarLowerStarAdjunction AddCommGrpCat.{u + 1} q).unit.app F₀ ≫
        (lowerStar AddCommGrpCat.{u + 1} q).map
          (α ≫ (upperStarLowerStarAdjunction AddCommGrpCat.{u + 1} p).unit.app F₁ ≫
            (lowerStar AddCommGrpCat.{u + 1} p).map β) ≫
        (lowerStarComp AddCommGrpCat.{u + 1} p q r hr).hom.app F₂ := by
  simp only [Functor.map_comp, ← Category.assoc]
  rw [upperStarComp_hom_app_unit_app AddCommGrpCat.{u + 1} p q F₀ r hr,
    Adjunction.comp_unit_app]
  simp only [Category.assoc]
  rw [← (lowerStarComp AddCommGrpCat.{u + 1} p q r hr).hom.naturality_assoc,
    ← (lowerStarComp AddCommGrpCat.{u + 1} p q r hr).hom.naturality]
  dsimp only [Functor.comp_map]
  simp only [← Functor.map_comp, ← Category.assoc]
  have hn := (upperStarLowerStarAdjunction AddCommGrpCat.{u + 1} p).unit.naturality α
  dsimp only [Functor.comp_map, Functor.id_map] at hn
  rw [hn]
  simp only [Functor.map_comp, Category.assoc]

-- Evaluate the transposition equation and transport along the geometric comparisons.
private theorem section_comp
    {R S T : Scheme.{u}} (p : T ⟶ S) (q : S ⟶ R) (r : T ⟶ R)
    (hr : r = p ≫ q)
    (F₀ : Sheaf R.smallEtaleTopology AddCommGrpCat.{u + 1})
    (F₁ : Sheaf S.smallEtaleTopology AddCommGrpCat.{u + 1})
    (F₂ : Sheaf T.smallEtaleTopology AddCommGrpCat.{u + 1})
    (α : (upperStar AddCommGrpCat.{u + 1} q).obj F₀ ⟶ F₁)
    (β : (upperStar AddCommGrpCat.{u + 1} p).obj F₁ ⟶ F₂)
    (U : R.Etale) (V : S.Etale) (W : T.Etale)
    (e : (MorphismProperty.Over.pullback @Etale ⊤ q).obj U ≅ V)
    (d : (MorphismProperty.Over.pullback @Etale ⊤ p).obj V ≅ W)
    (z : (MorphismProperty.Over.pullback @Etale ⊤ r).obj U ≅ W)
    (hz : z.inv ≫ (MorphismProperty.Over.pullbackComp p q r hr).hom.app U =
      d.inv ≫ (MorphismProperty.Over.pullback @Etale ⊤ p).map e.inv) :
    ((upperStarLowerStarAdjunction AddCommGrpCat.{u + 1} r).unit.app F₀).hom.app
        (op U) ≫
      ((upperStarComp AddCommGrpCat.{u + 1} p q r hr).hom.app F₀ ≫
        (upperStar AddCommGrpCat.{u + 1} p).map α ≫ β).hom.app
          (op ((MorphismProperty.Over.pullback @Etale ⊤ r).obj U)) ≫
      F₂.obj.map z.inv.op =
    ((upperStarLowerStarAdjunction AddCommGrpCat.{u + 1} q).unit.app F₀).hom.app
        (op U) ≫ α.hom.app (op ((MorphismProperty.Over.pullback @Etale ⊤ q).obj U)) ≫
      F₁.obj.map e.inv.op ≫
      ((upperStarLowerStarAdjunction AddCommGrpCat.{u + 1} p).unit.app F₁).hom.app
        (op V) ≫ β.hom.app (op ((MorphismProperty.Over.pullback @Etale ⊤ p).obj V)) ≫
      F₂.obj.map d.inv.op := by
  have ht := congrArg (fun f ↦ f.hom.app (op U))
    (transpose_comp p q r hr F₀ F₁ F₂ α β)
  have hn := (((upperStarLowerStarAdjunction AddCommGrpCat.{u + 1} p).unit.app F₁) ≫
    (lowerStar AddCommGrpCat.{u + 1} p).map β).hom.naturality e.inv.op
  dsimp only [ObjectProperty.FullSubcategory.comp_hom, NatTrans.comp_app] at ht hn
  simp only [lowerStar_map_hom_app] at ht hn
  simp only [lowerStarComp, Functor.sheafPushforwardContinuousComp'_hom_app_hom_app,
    Iso.symm_inv] at ht
  rw [← Category.assoc, ht]
  simp only [Category.assoc]
  rw [← F₂.obj.map_comp, ← op_comp, hz, op_comp, F₂.obj.map_comp]
  change F₁.obj.map e.inv.op ≫
      ((upperStarLowerStarAdjunction AddCommGrpCat.{u + 1} p).unit.app F₁).hom.app
        (op V) ≫ β.hom.app (op ((MorphismProperty.Over.pullback @Etale ⊤ p).obj V)) =
    (((upperStarLowerStarAdjunction AddCommGrpCat.{u + 1} p).unit.app F₁).hom.app
      (op ((MorphismProperty.Over.pullback @Etale ⊤ q).obj U)) ≫
      β.hom.app (op ((MorphismProperty.Over.pullback @Etale ⊤ p).obj
        ((MorphismProperty.Over.pullback @Etale ⊤ q).obj U)))) ≫
      F₂.obj.map ((MorphismProperty.Over.pullback @Etale ⊤ p).map e.inv).op at hn
  simp only [ObjectProperty.FullSubcategory.comp_hom, NatTrans.comp_app,
    lowerStar_map_hom_app, Category.assoc]
  rw [reassoc_of% hn]

-- The prescribed projections identify the two ways to paste three base changes.
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
private theorem transport_pasting
    {S₀ R S T : Scheme.{u}} (x : R ⟶ S₀) (y : S ⟶ S₀) (w : T ⟶ S₀)
    (p : T ⟶ S) (q : S ⟶ R) (r : T ⟶ R) (hr : r = p ≫ q) (X : S₀.Etale)
    (e : (MorphismProperty.Over.pullback @Etale ⊤ q).obj
      ((MorphismProperty.Over.pullback @Etale ⊤ x).obj X) ≅
        (MorphismProperty.Over.pullback @Etale ⊤ y).obj X)
    (d : (MorphismProperty.Over.pullback @Etale ⊤ p).obj
      ((MorphismProperty.Over.pullback @Etale ⊤ y).obj X) ≅
        (MorphismProperty.Over.pullback @Etale ⊤ w).obj X)
    (z : (MorphismProperty.Over.pullback @Etale ⊤ r).obj
      ((MorphismProperty.Over.pullback @Etale ⊤ x).obj X) ≅
        (MorphismProperty.Over.pullback @Etale ⊤ w).obj X)
    (he : e.hom.left ≫ pullback.fst X.hom y =
      pullback.fst ((MorphismProperty.Over.pullback @Etale ⊤ x).obj X).hom q ≫
        pullback.fst X.hom x)
    (hd : d.hom.left ≫ pullback.fst X.hom w =
      pullback.fst ((MorphismProperty.Over.pullback @Etale ⊤ y).obj X).hom p ≫
        pullback.fst X.hom y)
    (hz : z.hom.left ≫ pullback.fst X.hom w =
      pullback.fst ((MorphismProperty.Over.pullback @Etale ⊤ x).obj X).hom r ≫
        pullback.fst X.hom x) :
    z.inv ≫ (MorphismProperty.Over.pullbackComp p q r hr).hom.app
        ((MorphismProperty.Over.pullback @Etale ⊤ x).obj X) =
      d.inv ≫ (MorphismProperty.Over.pullback @Etale ⊤ p).map e.inv := by
  subst r
  have hh : (MorphismProperty.Over.pullbackComp p q (p ≫ q) rfl).hom.app
      ((MorphismProperty.Over.pullback @Etale ⊤ x).obj X) ≫
      (MorphismProperty.Over.pullback @Etale ⊤ p).map e.hom ≫ d.hom = z.hom := by
    ext1
    apply pullback.hom_ext
    · simp only [MorphismProperty.Comma.comp_left, Category.assoc]
      erw [hd, ← Category.assoc]
      rw [MorphismProperty.Over.pullback_map_left]
      simp only [Category.assoc]
      erw [pullback.lift_fst_assoc]
      simp only [Category.assoc]
      erw [he, ← Category.assoc, ← Category.assoc]
      have hp := MorphismProperty.Over.pullbackComp_left_fst_fst
        (P := @Etale) (Q := ⊤) p q
        ((MorphismProperty.Over.pullback @Etale ⊤ x).obj X)
      simpa only [Category.assoc, MorphismProperty.Over.pullback_obj_hom] using
        (congrArg (· ≫ pullback.fst X.hom x) hp).trans hz.symm
    · have h := MorphismProperty.Over.w z.hom
      simpa only [MorphismProperty.Comma.comp_left, Category.assoc,
        MorphismProperty.Over.pullback_obj_hom] using
        ((MorphismProperty.Over.w
          ((MorphismProperty.Over.pullbackComp p q (p ≫ q) rfl).hom.app
            ((MorphismProperty.Over.pullback @Etale ⊤ x).obj X) ≫
            (MorphismProperty.Over.pullback @Etale ⊤ p).map e.hom ≫ d.hom)).trans h.symm)
  apply (cancel_mono ((MorphismProperty.Over.pullback @Etale ⊤ p).map e.hom ≫ d.hom)).1
  simp only [Category.assoc, ← Functor.map_comp_assoc, e.inv_hom_id]
  erw [CategoryTheory.Functor.map_id]
  simp only [Category.id_comp, d.inv_hom_id]
  rw [hh, z.inv_hom_id]

-- The identity transpose is restriction along the identity pullback isomorphism.
private theorem section_identity
    {R : Scheme.{u}} (F : Sheaf R.smallEtaleTopology AddCommGrpCat.{u + 1}) (U : R.Etale)
    (α : (upperStar AddCommGrpCat.{u + 1} (𝟙 R)).obj F ⟶ F)
    (hα : α = (upperStarId AddCommGrpCat.{u + 1} R).hom.app F)
    (e : (MorphismProperty.Over.pullback @Etale ⊤ (𝟙 R)).obj U ≅ U)
    (he : e.hom.left = pullback.fst U.hom (𝟙 R)) :
    ((upperStarLowerStarAdjunction AddCommGrpCat.{u + 1} (𝟙 R)).unit.app F).hom.app (op U) ≫
      α.hom.app (op ((MorphismProperty.Over.pullback @Etale ⊤ (𝟙 R)).obj U)) ≫
      F.obj.map e.inv.op = 𝟙 _ := by
  have hh : e.hom = (MorphismProperty.Over.pullbackId @Etale ⊤ R).hom.app U := by
    apply MorphismProperty.Over.Hom.ext
    simpa only [MorphismProperty.Over.pullbackId_hom_app_left] using he
  rw [hα]
  have ht := congrArg (fun f ↦ f.hom.app (op U))
    (upperStarId_hom_app_unit_app AddCommGrpCat.{u + 1} R F)
  dsimp only [ObjectProperty.FullSubcategory.comp_hom, NatTrans.comp_app] at ht
  simp only [lowerStar_map_hom_app] at ht
  rw [← Category.assoc, ht]
  simp only [lowerStarId, GrothendieckTopology.lowerStarId,
    Functor.sheafPushforwardContinuousId'_inv_app_hom_app]
  rw [← F.obj.map_comp, ← op_comp]
  rw [← hh, e.inv_hom_id, op_id, CategoryTheory.Functor.map_id]
  rfl

-- Keep reflexive functor transport abstract, so the kernel need not unfold sheafification.
private theorem reflexive_functor_transport
    {C D : Type*} [Category C] [Category D] (H : C ⥤ D) (X : C) (h : H = H) :
    (eqToIso h).hom.app X = 𝟙 _ := by
  cases h
  rfl

-- Equality elimination takes place with abstract functors rather than their constructions.
private theorem transport_section_identity
    {Q C E : Type*} [Category C] [Category E]
    (H : Q → C ⥤ C) (B : Q → E ⥤ E) (F : C) (U : E)
    (q q₀ : Q) (h : q = q₀) (α₀ : (H q₀).obj F ⟶ F)
    (P : ∀ q, ((H q).obj F ⟶ F) → ((B q).obj U ≅ U) → Prop)
    (hP : ∀ e, P q₀ α₀ e)
    (α : (H q).obj F ⟶ F)
    (hα : α = (eqToIso (congrArg H h)).hom.app F ≫ α₀)
    (e : (B q).obj U ≅ U) : P q α e := by
  subst q
  rw [reflexive_functor_transport, Category.id_comp] at hα
  subst α
  exact hP e

private theorem section_id
    {R : Scheme.{u}} (q : R ⟶ R) (hq : q = 𝟙 R)
    (F : Sheaf R.smallEtaleTopology AddCommGrpCat.{u + 1}) (U : R.Etale)
    (α : (upperStar AddCommGrpCat.{u + 1} q).obj F ⟶ F)
    (hα : α = (eqToIso (congrArg (upperStar AddCommGrpCat.{u + 1}) hq)).hom.app F ≫
      (upperStarId AddCommGrpCat.{u + 1} R).hom.app F)
    (e : (MorphismProperty.Over.pullback @Etale ⊤ q).obj U ≅ U)
    (he : e.hom.left = pullback.fst U.hom q) :
    ((upperStarLowerStarAdjunction AddCommGrpCat.{u + 1} q).unit.app F).hom.app (op U) ≫
      α.hom.app (op ((MorphismProperty.Over.pullback @Etale ⊤ q).obj U)) ≫
      F.obj.map e.inv.op = 𝟙 _ := by
  let P := fun (q : R ⟶ R)
      (α : (upperStar AddCommGrpCat.{u + 1} q).obj F ⟶ F)
      (e : (MorphismProperty.Over.pullback @Etale ⊤ q).obj U ≅ U) ↦
    e.hom.left = pullback.fst U.hom q →
      ((upperStarLowerStarAdjunction AddCommGrpCat.{u + 1} q).unit.app F).hom.app
          (op U) ≫
        α.hom.app (op ((MorphismProperty.Over.pullback @Etale ⊤ q).obj U)) ≫
        F.obj.map e.inv.op = 𝟙 _
  have hP : ∀ e, P (𝟙 R) ((upperStarId AddCommGrpCat.{u + 1} R).hom.app F) e := by
    intro e he
    exact section_identity F U _ rfl e he
  let B : (R ⟶ R) → R.Etale ⥤ R.Etale := fun q ↦
    MorphismProperty.Over.pullback @Etale ⊤ q
  have hresult : P q α e := transport_section_identity
    (upperStar AddCommGrpCat.{u + 1}) B
    F U q (𝟙 R) hq ((upperStarId AddCommGrpCat.{u + 1} R).hom.app F)
    P hP α hα e
  exact hresult he

/-- The displayed stage maps form a diagram and the limit maps form a cocone.
Source: Stacks Project, Sites, Tag 09YN, proof of lemma-colimit, and Etale
Cohomology, Tag 09YQ, inverse-image composition comparisons.
(blueprint: lem-weil-pbc-etale-limit-scalar-section-map-laws).

Proof: The first-projection equations and the equations over the base determine
all pullback comparisons uniquely. Pullback uniqueness therefore gives the identity
and composition laws for gamma and the compatibility of gamma with delta.
Transpose the stage maps through the inverse-image adjunction. Naturality of its
unit, the identity and composition assumptions on phi, and the preceding pullback
laws give the identity and composition equations for rho. Transpose the cocone
legs in the same way. The transition formula hG and cocone naturality of L then
give rho followed by mu equal to mu. These calculations use no continuity theorem,
and remain valid on empty objects and for zero sheaves. -/
theorem etale_limit_scalar_section_map_laws
    {I : Type u} [Preorder I]
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
    (i₀ : I) (T₀ : (D.obj (op i₀)).Etale) :
    let J := {j : I // i₀ ≤ j}
    let Tj := fun j : J ↦
      (MorphismProperty.Over.pullback @Etale ⊤
        (D.map (homOfLE j.property).op)).obj T₀
    let Tlim := (MorphismProperty.Over.pullback @Etale ⊤ (c.π.app (op i₀))).obj T₀
    ∀ (γ : ∀ (j k : J) (a : j ⟶ k),
        (MorphismProperty.Over.pullback @Etale ⊤
          (D.map (show j.val ⟶ k.val from a).op)).obj (Tj j) ≅ Tj k)
      (δ : ∀ j : J,
        (MorphismProperty.Over.pullback @Etale ⊤ (c.π.app (op j.val))).obj (Tj j) ≅ Tlim),
      (∀ (j k : J) (a : j ⟶ k),
        (γ j k a).hom.left ≫ pullback.fst T₀.hom (D.map (homOfLE k.property).op) =
          pullback.fst (Tj j).hom (D.map (show j.val ⟶ k.val from a).op) ≫
            pullback.fst T₀.hom (D.map (homOfLE j.property).op)) →
      (∀ j : J,
        (δ j).hom.left ≫ pullback.fst T₀.hom (c.π.app (op i₀)) =
          pullback.fst (Tj j).hom (c.π.app (op j.val)) ≫
            pullback.fst T₀.hom (D.map (homOfLE j.property).op)) →
    let ρ := fun (j k : J) (a : j ⟶ k) ↦
      ((upperStarLowerStarAdjunction AddCommGrpCat.{u + 1}
        (D.map (show j.val ⟶ k.val from a).op)).unit.app (F j.val)).hom.app (op (Tj j)) ≫
        (φ (show j.val ⟶ k.val from a)).hom.app
          (op ((MorphismProperty.Over.pullback @Etale ⊤
            (D.map (show j.val ⟶ k.val from a).op)).obj (Tj j))) ≫
        (F k.val).obj.map (γ j k a).inv.op
    let μ := fun j : J ↦
      ((upperStarLowerStarAdjunction AddCommGrpCat.{u + 1}
        (c.π.app (op j.val))).unit.app (F j.val)).hom.app (op (Tj j)) ≫
        (eG j.val).inv.hom.app
          (op ((MorphismProperty.Over.pullback @Etale ⊤
            (c.π.app (op j.val))).obj (Tj j))) ≫
        (L.ι.app j.val).hom.app
          (op ((MorphismProperty.Over.pullback @Etale ⊤
            (c.π.app (op j.val))).obj (Tj j))) ≫
        L.pt.obj.map (δ j).inv.op
    (∀ j : J, ρ j j (𝟙 j) = 𝟙 _) ∧
    (∀ (j k l : J) (a : j ⟶ k) (b : k ⟶ l),
      ρ j l (a ≫ b) = ρ j k a ≫ ρ k l b) ∧
    (∀ (j k : J) (a : j ⟶ k), ρ j k a ≫ μ k = μ j) := by
  intro J Tj Tlim γ δ hγ hδ ρ μ
  refine ⟨?_, ?_, ?_⟩
  · intro j
    let σ := fun (f : j.val ⟶ j.val) ↦
      ((upperStarLowerStarAdjunction AddCommGrpCat.{u + 1} (D.map f.op)).unit.app
        (F j.val)).hom.app (op (Tj j)) ≫
      (φ f).hom.app
        (op ((MorphismProperty.Over.pullback @Etale ⊤ (D.map f.op)).obj (Tj j))) ≫
      (F j.val).obj.map (γ j j (show j ⟶ j from f)).inv.op
    change σ (show j.val ⟶ j.val from 𝟙 j) = 𝟙 _
    have hi : (show j.val ⟶ j.val from 𝟙 j) = 𝟙 j.val := rfl
    apply (congrArg σ hi).trans
    apply section_id _ (D.map_id (op j.val)) (F j.val) (Tj j)
      (φ (𝟙 j.val)) (hidentity j.val) (γ j j (show j ⟶ j from 𝟙 j.val))
    apply pullback.hom_ext
    · exact hγ j j (show j ⟶ j from 𝟙 j.val)
    · have hw := MorphismProperty.Over.w (γ j j (show j ⟶ j from 𝟙 j.val)).hom
      dsimp only [Tj] at hw ⊢
      simp only [MorphismProperty.Over.pullback_obj_hom] at hw
      erw [hw, pullback.condition, D.map_id, Category.comp_id]
  · intro j k l a b
    have hp := transport_pasting
      (D.map (homOfLE j.property).op) (D.map (homOfLE k.property).op)
      (D.map (homOfLE l.property).op)
      (D.map (show k.val ⟶ l.val from b).op)
      (D.map (show j.val ⟶ k.val from a).op)
      (D.map (show j.val ⟶ l.val from a ≫ b).op)
      (D.map_comp (show k.val ⟶ l.val from b).op (show j.val ⟶ k.val from a).op) T₀
      (γ j k a) (γ k l b) (γ j l (a ≫ b))
      (hγ j k a) (hγ k l b) (hγ j l (a ≫ b))
    have hs := section_comp (D.map (show k.val ⟶ l.val from b).op)
      (D.map (show j.val ⟶ k.val from a).op)
      (D.map (show j.val ⟶ l.val from a ≫ b).op)
      (D.map_comp (show k.val ⟶ l.val from b).op (show j.val ⟶ k.val from a).op)
      (F j.val) (F k.val) (F l.val) (φ a) (φ b)
      (Tj j) (Tj k) (Tj l) (γ j k a) (γ k l b) (γ j l (a ≫ b)) hp
    rw [← hcomposition j.val k.val l.val a b] at hs
    dsimp only [ρ]
    simp only [Category.assoc]
    dsimp only [Preorder.smallCategory] at hs ⊢
    exact hs
  · intro j k a
    have hleg :
        (upperStarComp AddCommGrpCat.{u + 1} (c.π.app (op k.val))
          (D.map (show j.val ⟶ k.val from a).op) (c.π.app (op j.val))
          (c.w (show j.val ⟶ k.val from a).op).symm).hom.app (F j.val) ≫
          (upperStar AddCommGrpCat.{u + 1} (c.π.app (op k.val))).map (φ a) ≫
          ((eG k.val).inv ≫ L.ι.app k.val) =
        (eG j.val).inv ≫ L.ι.app j.val := by
      apply (cancel_epi (eG j.val).hom).1
      rw [(eG j.val).hom_inv_id_assoc, ← L.w (show j.val ⟶ k.val from a),
        hG j.val k.val a]
      simp only [Category.assoc]
    have hp := transport_pasting
      (D.map (homOfLE j.property).op) (D.map (homOfLE k.property).op)
      (c.π.app (op i₀)) (c.π.app (op k.val))
      (D.map (show j.val ⟶ k.val from a).op) (c.π.app (op j.val))
      (c.w (show j.val ⟶ k.val from a).op).symm T₀
      (γ j k a) (δ k) (δ j) (hγ j k a) (hδ k) (hδ j)
    have hs := section_comp (c.π.app (op k.val))
      (D.map (show j.val ⟶ k.val from a).op) (c.π.app (op j.val))
      (c.w (show j.val ⟶ k.val from a).op).symm
      (F j.val) (F k.val) L.pt (φ a) ((eG k.val).inv ≫ L.ι.app k.val)
      (Tj j) (Tj k) Tlim (γ j k a) (δ k) (δ j) hp
    rw [hleg] at hs
    simpa only [ρ, μ, ObjectProperty.FullSubcategory.comp_hom, NatTrans.comp_app,
      Category.assoc] using hs.symm

end AlgebraicGeometry.Etale
