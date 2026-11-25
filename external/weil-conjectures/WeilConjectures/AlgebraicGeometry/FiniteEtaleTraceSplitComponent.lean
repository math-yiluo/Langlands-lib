/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.FiniteEtaleTrace

/-!
# The trace composite on a split étale-site object

Source: Stacks Project, Tag 03SH (section-trace-method), paragraph after
Definition 03SE.
(blueprint: lem-weil-pbc-finite-etale-trace-split-component).
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Etale

private theorem restriction_localization {X Y : Scheme.{u}} (f : Y ⟶ X)
    [IsFinite f] [Etale f] (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1})
    (W : X.Etale) :
    (finiteEtaleRestriction f F).hom.app (op W) ≫
      ((upperStarIsoLocalizationRestriction AddCommGrpCat.{u + 1} f inferInstance).app
        F).hom.hom.app (op ((MorphismProperty.Over.pullback @Etale ⊤ f).obj W)) =
      F.obj.map ((MorphismProperty.Over.mapPullbackAdj @Etale ⊤ f inferInstance
        trivial).counit.app W).op := by
  have h := Adjunction.unit_leftAdjointUniq_hom_app
    (upperStarLowerStarAdjunction AddCommGrpCat.{u + 1} f)
    (localizationRestrictionLowerStarAdjunction AddCommGrpCat.{u + 1} f inferInstance) F
  have hw := NatTrans.congr_app (Sheaf.hom_ext_iff.1 h) (op W)
  change (finiteEtaleRestriction f F).hom.app (op W) ≫
    ((upperStarIsoLocalizationRestriction AddCommGrpCat.{u + 1} f inferInstance).app
      F).hom.hom.app (op ((MorphismProperty.Over.pullback @Etale ⊤ f).obj W)) =
    ((localizationRestrictionLowerStarAdjunction AddCommGrpCat.{u + 1} f
      inferInstance).unit.app F).hom.app (op W) at hw
  rw [hw]
  simp [localizationRestrictionLowerStarAdjunction, Adjunction.sheafPushforwardContinuous,
    Adjunction.whiskerLeft]

private theorem split_component_localized
    {X Y U : Scheme.{u}} (f : Y ⟶ X) [IsFinite f] [Etale f]
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1})
    (g : U ⟶ X) (hg : Etale g) (J : Type u) [Fintype J]
    (D : J → Scheme.{u}) (i : ∀ j, D j ⟶ pullback f g) (t : ∀ j, U ⟶ D j)
    (hc : IsColimit (Cofan.mk (pullback f g) i))
    (ht₁ : ∀ j, t j ≫ i j ≫ pullback.snd f g = 𝟙 U)
    (ht₂ : ∀ j, i j ≫ pullback.snd f g ≫ t j = 𝟙 (D j))
    (hi : ∀ j, IsOpenImmersion (i j) ∧ IsClosedImmersion (i j))
    (Z : U.Etale) :
    let W : X.Etale := (MorphismProperty.Over.map ⊤ hg).obj Z
    (finiteEtaleRestriction f F ≫ finiteEtaleTrace f F).hom.app (op W) =
      Fintype.card J • 𝟙 (F.obj.obj (op W)) := by
  classical
  let A := AddCommGrpCat.{u + 1}
  let := hg
  let f' := pullback.snd f g
  let hf' : Etale f' := inferInstance
  let F' := (upperStar A g).obj F
  let W : X.Etale := (MorphismProperty.Over.map ⊤ hg).obj Z
  let B := fun {S T : Scheme.{u}} (a : T ⟶ S) (ha : Etale a) (Z : S.Etale) ↦
    (MorphismProperty.Over.map ⊤ ha).obj
      ((MorphismProperty.Over.pullback @Etale ⊤ a).obj Z)
  let k : pullback Z.hom f' ⟶ pullback (Z.hom ≫ g) f :=
    pullback.lift (pullback.fst Z.hom f')
      (pullback.snd Z.hom f' ≫ pullback.fst f g) (by
        rw [Category.assoc, pullback.condition, ← Category.assoc, pullback.condition]
        simp [f'])
  let l : pullback (Z.hom ≫ g) f ⟶ pullback Z.hom f' :=
    pullback.lift (pullback.fst (Z.hom ≫ g) f)
      (pullback.lift (pullback.snd (Z.hom ≫ g) f)
        (pullback.fst (Z.hom ≫ g) f ≫ Z.hom) (by
          rw [Category.assoc, ← pullback.condition])) (by simp [f'])
  let q : pullback Z.hom f' ≅ pullback (Z.hom ≫ g) f :=
    { hom := k
      inv := l
      hom_inv_id := by
        apply pullback.hom_ext
        · simp [k, l]
        · apply pullback.hom_ext
          · simp [k, l]
          · simp [k, l, f', ← pullback.condition]
      inv_hom_id := by apply pullback.hom_ext <;> simp [k, l] }
  let κ : (MorphismProperty.Over.map ⊤ hg).obj (B f' hf' Z) ≅ B f inferInstance W :=
    MorphismProperty.Over.isoMk q (by
      change k ≫ (pullback.snd (Z.hom ≫ g) f ≫ f) =
        (pullback.snd Z.hom f' ≫ f') ≫ g
      dsimp only [k]
      rw [← Category.assoc, pullback.lift_snd, Category.assoc, pullback.condition]
      rfl)
  have hk₁ : κ.hom.left ≫ pullback.fst (Z.hom ≫ g) f =
      pullback.fst Z.hom f' := by simp [κ, q, k]
  have hk₂ : κ.hom.left ≫ pullback.snd (Z.hom ≫ g) f =
      pullback.snd Z.hom f' ≫ pullback.fst f g := by simp [κ, q, k]
  let σ (j : J) : Z ⟶ B f' hf' Z := MorphismProperty.Over.homMk
    (pullback.lift (𝟙 Z.left) (Z.hom ≫ t j ≫ i j)
      (by simp [Category.assoc, f', ht₁])) (by simp [B, Category.assoc, f', ht₁])
  have hp := Classical.choose_spec existsUnique_finiteEtaleTrace.exists
  have hs := hp.2.2 U (pullback f g) f' inferInstance hf' F' J D i t hc
    ht₁ ht₂ (fun j ↦ (hi j).1) (fun j ↦ (hi j).2) Z
  have hl := hp.2.1 X Y U f inferInstance inferInstance g hg F Z κ hk₁ hk₂
  change _ ≫ (finiteEtaleTrace f' F').hom.app (op Z) =
    ∑ j, F'.obj.map (σ j).op at hs
  change _ ≫ (finiteEtaleTrace f' F').hom.app (op Z) ≫ _ =
    _ ≫ F.obj.map κ.inv.op ≫ _ ≫ (finiteEtaleTrace f F).hom.app (op W) at hl
  rw [← Category.assoc, hs, Preadditive.sum_comp] at hl
  let ρ := (upperStarIsoLocalizationRestriction A g hg).app F
  have hn (j : J) : F'.obj.map (σ j).op ≫ ρ.hom.hom.app (op Z) =
      ρ.hom.hom.app (op (B f' hf' Z)) ≫
        F.obj.map ((MorphismProperty.Over.map ⊤ hg).map (σ j)).op := by
    exact ρ.hom.hom.naturality (σ j).op
  change (∑ j, F'.obj.map (σ j).op ≫ ρ.hom.hom.app (op Z)) =
    ρ.hom.hom.app (op (B f' hf' Z)) ≫ F.obj.map κ.inv.op ≫
      ((upperStarIsoLocalizationRestriction A f inferInstance).app F).inv.hom.app
        (op ((MorphismProperty.Over.pullback @Etale ⊤ f).obj W)) ≫
      (finiteEtaleTrace f F).hom.app (op W) at hl
  simp_rw [hn] at hl
  rw [← Preadditive.comp_sum] at hl
  have hbar := (cancel_epi (ρ.hom.hom.app (op (B f' hf' Z)))).mp hl.symm
  have hbar' := congrArg (fun a ↦ F.obj.map κ.hom.op ≫ a) hbar
  simp only [← Category.assoc, ← F.obj.map_comp, ← op_comp, Iso.inv_hom_id,
    op_id, F.obj.map_id, Category.id_comp, Preadditive.comp_sum] at hbar'
  let p := (MorphismProperty.Over.mapPullbackAdj @Etale ⊤ f inferInstance
    trivial).counit.app W
  have hu := restriction_localization f F W
  let c := (upperStarIsoLocalizationRestriction A f inferInstance).app F
  have hid : c.hom.hom.app (op ((MorphismProperty.Over.pullback @Etale ⊤ f).obj W)) ≫
      c.inv.hom.app (op ((MorphismProperty.Over.pullback @Etale ⊤ f).obj W)) =
      𝟙 (((upperStar A f).obj F).obj.obj
        (op ((MorphismProperty.Over.pullback @Etale ⊤ f).obj W))) := by
    rw [← NatTrans.comp_app, ← ObjectProperty.FullSubcategory.comp_hom]
    simp only [Iso.hom_inv_id, ObjectProperty.FullSubcategory.id_hom, NatTrans.id_app]
  have hsection (j : J) :
      ((MorphismProperty.Over.map ⊤ hg).map (σ j) ≫ κ.hom) ≫ p = 𝟙 W := by
    ext
    change (σ j).left ≫ κ.hom.left ≫ pullback.fst (Z.hom ≫ g) f = 𝟙 Z.left
    rw [hk₁]
    simp [σ]
  change (finiteEtaleRestriction f F).hom.app (op W) ≫
    (finiteEtaleTrace f F).hom.app (op W) = _
  calc
    _ = ((finiteEtaleRestriction f F).hom.app (op W) ≫
        c.hom.hom.app (op ((MorphismProperty.Over.pullback @Etale ⊤ f).obj W))) ≫
        (c.inv.hom.app (op ((MorphismProperty.Over.pullback @Etale ⊤ f).obj W)) ≫
          (finiteEtaleTrace f F).hom.app (op W)) := by
      rw [Category.assoc, ← Category.assoc _ _ ((finiteEtaleTrace f F).hom.app (op W)),
        hid]
      change (finiteEtaleRestriction f F).hom.app (op W) ≫
        (finiteEtaleTrace f F).hom.app (op W) =
          (finiteEtaleRestriction f F).hom.app (op W) ≫
            𝟙 (((lowerStar A f).obj ((upperStar A f).obj F)).obj.obj (op W)) ≫
              (finiteEtaleTrace f F).hom.app (op W)
      exact (Category.id_comp
        ((finiteEtaleTrace f F).hom.app (op W))).symm ▸ rfl
    _ = F.obj.map p.op ≫ ∑ j,
        F.obj.map ((MorphismProperty.Over.map ⊤ hg).map (σ j) ≫ κ.hom).op := by
      rw [hu, hbar']
    _ = ∑ _j : J, 𝟙 (F.obj.obj (op W)) := by
      rw [Preadditive.comp_sum]
      apply Finset.sum_congr rfl
      intro j hj
      rw [← F.obj.map_comp, ← op_comp, hsection, op_id]
      exact F.obj.map_id (op W)
    _ = Fintype.card J • 𝟙 (F.obj.obj (op W)) := by simp only [Finset.sum_const,
      Finset.card_univ]

/-- On a site object whose pulled-back cover has a given finite clopen splitting,
trace after restriction is the sum of one identity per piece. No degree or connectedness
hypothesis is used. Source: Stacks Project, Tag 03SH (section-trace-method), paragraph
following Definition 03SE.
(blueprint: lem-weil-pbc-finite-etale-trace-split-component).

Proof:
1. Identify inverse image with localization restriction using
   `upperStarIsoLocalizationRestriction`. Under this isomorphism the adjunction unit
   on `W` is restriction along the projection `W ×_X Y → W`.
2. Use property (1), localization compatibility, of `existsUnique_finiteEtaleTrace`
   for `W.hom`. Pullback symmetry and pasting identify its site-object fibre product
   with `Y ×_X W`; transport the supplied clopen splitting across this identification.
3. Invert the isomorphisms `i j ≫ pullback.snd f W.hom` to obtain sections of the
   projection. Property (2), the split formula, of the same trace characterization
   expresses trace as the sum of restriction along these sections.
4. Each section composed with the projection is the identity. Contravariant
   functoriality therefore makes the composite of restriction with each summand the
   identity of `F(W)`. Distribute composition over the finite sum and use
   `Finset.sum_const` to obtain `Fintype.card J` times the identity. Transport back
   through the localization isomorphisms, which cancel by their inverse laws.
   This includes an empty index set: the empty sum is zero, agreeing with `0 • id`.
   An empty `W` also causes no difficulty, since the empty covering forces `F(W)=0`. -/
theorem finiteEtaleTrace_comp_restriction_app_of_split
    {X Y : Scheme.{u}} (f : Y ⟶ X) [IsFinite f] [Etale f]
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}) (W : X.Etale)
    (J : Type u) [Fintype J] (D : J → Scheme.{u})
    (i : ∀ j, D j ⟶ pullback f W.hom)
    (_ : Nonempty (IsColimit (Cofan.mk (pullback f W.hom) i)))
    (_ : ∀ j, IsOpenImmersion (i j) ∧ IsClosedImmersion (i j))
    (_ : ∀ j, IsIso (i j ≫ pullback.snd f W.hom)) :
    (finiteEtaleRestriction f F ≫ finiteEtaleTrace f F).hom.app (op W) =
      Fintype.card J • 𝟙 (F.obj.obj (op W)) := by
  classical
  rename_i hc himm hiso
  let (j : J) : IsIso (i j ≫ pullback.snd f W.hom) := hiso j
  let t : ∀ j, W.left ⟶ D j := fun j ↦ inv (i j ≫ pullback.snd f W.hom)
  have ht₁ (j : J) : t j ≫ i j ≫ pullback.snd f W.hom = 𝟙 W.left := by
    simp [t]
  have ht₂ (j : J) : i j ≫ pullback.snd f W.hom ≫ t j = 𝟙 (D j) := by
    simp [t, ← Category.assoc]
  let Z : W.left.Etale := Scheme.Etale.mk (𝟙 W.left)
  have h := split_component_localized f F W.hom W.prop J D i t hc.some ht₁ ht₂ himm Z
  let W' : X.Etale := (MorphismProperty.Over.map ⊤ W.prop).obj Z
  let e : W' ≅ W := MorphismProperty.Over.isoMk (Iso.refl W.left) (by simp [W', Z])
  let C := finiteEtaleRestriction f F ≫ finiteEtaleTrace f F
  have hn := C.hom.naturality e.hom.op
  change F.obj.map e.hom.op ≫ C.hom.app (op W') =
    C.hom.app (op W) ≫ F.obj.map e.hom.op at hn
  change C.hom.app (op W') = _ at h
  rw [h] at hn
  have hn' := congrArg (fun a ↦ a ≫ F.obj.map e.inv.op) hn
  change (F.obj.map e.hom.op ≫ (Fintype.card J • 𝟙 (F.obj.obj (op W')))) ≫
      F.obj.map e.inv.op = (C.hom.app (op W) ≫ F.obj.map e.hom.op) ≫
        F.obj.map e.inv.op at hn'
  have he : F.obj.map e.hom.op ≫ F.obj.map e.inv.op =
      𝟙 (F.obj.obj (op W)) := by
    rw [← F.obj.map_comp, ← op_comp, Iso.inv_hom_id, op_id, F.obj.map_id]
  simp only [Preadditive.comp_nsmul, Preadditive.nsmul_comp, Category.comp_id,
    Category.assoc] at hn'
  rw [he, Category.comp_id] at hn'
  exact hn'.symm

end AlgebraicGeometry.Etale
