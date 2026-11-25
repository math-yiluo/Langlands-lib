/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.FiniteEtale
public import WeilConjectures.SixFunctors.Etale.LowerShriek.EtaleMap

/-!
# Nested summands in section-preserving support composition

Source: Stacks Project, Tags 0F4Y and 0F50
(blueprint: lem-sfb-etale-support-nested-summands).
-/

@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.Etale

/-- The structural summand inclusion followed by the ordinary direct-image comparison
is the graph extension. This converts the summand equation to an equality of sections. -/
private lemma unit_comp_toLowerStar
    (A : Type (u + 1)) [CommRing A]
    {X Y : Scheme.{u}} (f : X ⟶ Y) [Etale f] [IsSeparated f]
    (M : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A)) (W : X.Etale) :
    ((etaleLowerShriekRestrictionAdjunction (ModuleCat.{u + 1} A) f).unit.app M).hom.app
        (Opposite.op W) ≫
      (etaleLowerShriekToLowerStar (ModuleCat.{u + 1} A) f M).hom.app
        (Opposite.op ((MorphismProperty.Over.map ⊤ (inferInstance : Etale f)).obj W)) =
      Scheme.Etale.graphExtend f M W := by
  have h := (etaleLowerShriekRestrictionAdjunction (ModuleCat.{u + 1} A) f).homEquiv
    M _ |>.apply_symm_apply ((lowerStarUnit (ModuleCat.{u + 1} A) f).app M)
  rw [Adjunction.homEquiv_unit] at h
  exact congrArg (fun k => k.hom.app (Opposite.op W)) h

private lemma unit_comp_normalized_inclusion
    (A : Type (u + 1)) [CommRing A]
    {X Y : Scheme.{u}} (f : X ⟶ Y) [Etale f] [IsSeparated f]
    (F : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A) ⥤
      Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} A))
    (ι : F ⟶ lowerStar (ModuleCat.{u + 1} A) f)
    (o : etaleLowerShriek (ModuleCat.{u + 1} A) f inferInstance ≅ F)
    (M : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A))
    (n : o.hom.app M ≫ ι.app M = etaleLowerShriekToLowerStar (ModuleCat.{u + 1} A) f M)
    (W : X.Etale) :
    ((etaleLowerShriekRestrictionAdjunction (ModuleCat.{u + 1} A) f).unit.app M).hom.app
        (Opposite.op W) ≫
      (o.hom.app M).hom.app
        (Opposite.op ((MorphismProperty.Over.map ⊤ (inferInstance : Etale f)).obj W)) ≫
      (ι.app M).hom.app
        (Opposite.op ((MorphismProperty.Over.map ⊤ (inferInstance : Etale f)).obj W)) =
      Scheme.Etale.graphExtend f M W := by
  have hn := congrArg (fun k => k.hom.app
    (Opposite.op ((MorphismProperty.Over.map ⊤ (inferInstance : Etale f)).obj W))) n
  change (o.hom.app M).hom.app _ ≫ (ι.app M).hom.app _ = _ at hn
  rw [hn]
  exact unit_comp_toLowerStar A f M W

set_option backward.isDefEq.respectTransparency false in
private lemma graphExtend_zero_of_disjoint
    (A : Type (u + 1)) [CommRing A]
    {X Y : Scheme.{u}} (f : X ⟶ Y) [Etale f] [IsSeparated f]
    (M : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A))
    (W Z : X.Etale) (k : Z ⟶ Scheme.Etale.graphTarget f W)
    (hk : Disjoint (Set.range k.left) (Set.range (Scheme.Etale.graph f W).left)) :
    Scheme.Etale.graphExtend f M W ≫ M.obj.map k.op = 0 := by
  let l : Z ⟶ Scheme.Etale.graphComplObj f W :=
    MorphismProperty.Over.homMk
      (IsOpenImmersion.lift (Scheme.Etale.graphComplι f W).left k.left (by
        change Set.range k.left ⊆ Set.range (Scheme.Etale.graphCompl f W).ι
        rw [Scheme.Opens.range_ι]
        exact Set.disjoint_left.mp hk))
      (by
        change _ ≫ (Scheme.Etale.graphComplι f W).left ≫ _ = _
        rw [← Category.assoc, IsOpenImmersion.lift_fac]
        exact k.w) trivial
  have hl : l ≫ Scheme.Etale.graphComplι f W = k :=
    MorphismProperty.Over.Hom.ext (IsOpenImmersion.lift_fac _ _ _)
  rw [← hl, op_comp, Functor.map_comp,
    Scheme.Etale.graphExtend_graphComplι_assoc, zero_comp]

set_option backward.isDefEq.respectTransparency false in
private lemma graphExtend_comp
    (A : Type (u + 1)) [CommRing A]
    {V T B : Scheme.{u}} (h : V ⟶ T) (e : T ⟶ B) [Etale h] [Etale e]
    [IsSeparated h] [IsSeparated e]
    (M : Sheaf V.smallEtaleTopology (ModuleCat.{u + 1} A)) (W : V.Etale) :
    Scheme.Etale.graphExtend h M W ≫
      Scheme.Etale.graphExtend e ((lowerStar (ModuleCat.{u + 1} A) h).obj M)
        ((MorphismProperty.Over.map ⊤ (inferInstance : Etale h)).obj W) ≫
      ((lowerStarComp (ModuleCat.{u + 1} A) h e).hom.app M).hom.app
        (Opposite.op ((MorphismProperty.Over.map ⊤ (inferInstance : Etale e)).obj
          ((MorphismProperty.Over.map ⊤ (inferInstance : Etale h)).obj W))) =
    Scheme.Etale.graphExtend (h ≫ e) M W ≫ M.obj.map
      (((h ≫ e).Etale.map ((MorphismProperty.Over.mapComp ⊤
        (inferInstance : Etale h) (inferInstance : Etale e)).inv.app W))).op := by
  let Wh : T.Etale := (MorphismProperty.Over.map ⊤ (inferInstance : Etale h)).obj W
  let Whe : B.Etale := (MorphismProperty.Over.map ⊤ (inferInstance : Etale e)).obj Wh
  let c : Scheme.Etale.graphTarget (h ≫ e) W ≅ h.Etale.obj (e.Etale.obj Whe) :=
    (Functor.mapIso (h ≫ e).Etale
      ((MorphismProperty.Over.mapComp ⊤
        (inferInstance : Etale h) (inferInstance : Etale e)).app W)) ≪≫
      (MorphismProperty.Over.pullbackComp (P := @Etale) (Q := ⊤) h e).app Whe
  let j := h.Etale.map (Scheme.Etale.graph e Wh)
  have hj : Scheme.Etale.graph h W ≫ j = Scheme.Etale.graph (h ≫ e) W ≫ c.hom := by
    apply MorphismProperty.Over.Hom.ext
    change (Scheme.Etale.graph h W).left ≫ j.left =
      (Scheme.Etale.graph (h ≫ e) W).left ≫ c.hom.left
    dsimp only [c, Iso.trans_hom, NatTrans.comp_app, Functor.mapIso_hom]
    rw [MorphismProperty.Comma.comp_left]
    apply pullback.hom_ext
    · apply pullback.hom_ext <;>
        simp [Category.assoc, j, Wh, Whe, Scheme.Etale.graph_left,
          MorphismProperty.Over.pullbackComp_hom_app_left,
          Scheme.Hom.Etale, MorphismProperty.Over.pullback, MorphismProperty.Over.mapComp,
          Scheme.Etale.graphTarget, MorphismProperty.Over.mk]
      rfl
    · simp [Category.assoc, j, Wh, Whe, Scheme.Etale.graph_left,
        MorphismProperty.Over.pullbackComp_hom_app_left,
        Scheme.Hom.Etale, MorphismProperty.Over.pullback, MorphismProperty.Over.mapComp,
        Scheme.Etale.graphTarget, MorphismProperty.Over.mk]
  let l := h.Etale.map (Scheme.Etale.graphComplι e Wh)
  have hpj : IsPullback j.left (pullback.fst Wh.hom h)
      (pullback.fst (Scheme.Etale.graphTarget e Wh).hom h)
      (Scheme.Etale.graph e Wh).left := by
    refine IsPullback.of_right ?_ ?_
      (IsPullback.of_hasPullback (Scheme.Etale.graphTarget e Wh).hom h).flip
    · have hw : (Scheme.Etale.graph e Wh).left ≫
          (Scheme.Etale.graphTarget e Wh).hom = Wh.hom :=
        (Scheme.Etale.graph e Wh).w
      simpa only [j, Scheme.Hom.etale_map_left_comp_snd, hw] using
        (IsPullback.of_hasPullback Wh.hom h).flip
    · exact Scheme.Hom.etale_map_left_comp_fst h (Scheme.Etale.graph e Wh)
  have hjopen : IsOpenImmersion j.left := hpj.isOpenImmersion_fst
  have heq : Scheme.Etale.graphExtend h M W ≫
      Scheme.Etale.graphExtend e ((lowerStar (ModuleCat.{u + 1} A) h).obj M) Wh =
      Scheme.Etale.graphExtend (h ≫ e) M W ≫ M.obj.map c.inv.op := by
    apply Scheme.Etale.graph_hom_ext e ((lowerStar (ModuleCat.{u + 1} A) h).obj M)
    · change _ ≫ M.obj.map j.op = _ ≫ M.obj.map j.op
      have hg := Scheme.Etale.graphExtend_graph e
        ((lowerStar (ModuleCat.{u + 1} A) h).obj M) Wh
      change Scheme.Etale.graphExtend e
        ((lowerStar (ModuleCat.{u + 1} A) h).obj M) Wh ≫ M.obj.map j.op =
          𝟙 (M.obj.obj (Opposite.op (Scheme.Etale.graphTarget h W))) at hg
      rw [Category.assoc, hg, Category.comp_id]
      apply Scheme.Etale.graph_hom_ext h M
      · simp only [Category.assoc, ← Functor.map_comp, ← op_comp]
        have hk : Scheme.Etale.graph h W ≫ j ≫ c.inv =
            Scheme.Etale.graph (h ≫ e) W := by
          rw [← Category.assoc, hj, Category.assoc, c.hom_inv_id, Category.comp_id]
        rw [hk, Scheme.Etale.graphExtend_graph, Scheme.Etale.graphExtend_graph]
      · rw [Scheme.Etale.graphExtend_graphComplι]
        simp only [Category.assoc, ← Functor.map_comp, ← op_comp]
        symm
        apply graphExtend_zero_of_disjoint
        apply Set.disjoint_left.mpr
        rintro _ ⟨x, rfl⟩ ⟨y, hy⟩
        have hh := congrArg c.hom.left hy
        change (Scheme.Etale.graph (h ≫ e) W ≫ c.hom).left y =
          (Scheme.Etale.graphComplι h W ≫ j ≫ c.inv ≫ c.hom).left x at hh
        rw [c.inv_hom_id, Category.comp_id, ← hj] at hh
        have hy'' := j.left.isOpenEmbedding.injective hh
        exact Set.disjoint_left.mp (Scheme.Etale.isCompl_range_graph h W).disjoint
          ⟨y, hy''⟩ ⟨x, rfl⟩
    · change _ ≫ M.obj.map l.op = _ ≫ M.obj.map l.op
      have hg := Scheme.Etale.graphExtend_graphComplι e
        ((lowerStar (ModuleCat.{u + 1} A) h).obj M) Wh
      change Scheme.Etale.graphExtend e
        ((lowerStar (ModuleCat.{u + 1} A) h).obj M) Wh ≫ M.obj.map l.op = 0 at hg
      rw [Category.assoc, hg, comp_zero]
      simp only [← Functor.map_comp, ← op_comp, Category.assoc]
      symm
      apply graphExtend_zero_of_disjoint
      apply Set.disjoint_left.mpr
      rintro _ ⟨x, rfl⟩ ⟨y, hy⟩
      have hy' := congrArg (fun z =>
        (pullback.fst (Scheme.Etale.graphTarget e Wh).hom h) (c.hom.left z)) hy
      have hl : l.left ≫ pullback.fst (Scheme.Etale.graphTarget e Wh).hom h =
          pullback.fst (Scheme.Etale.graphComplObj e Wh).hom h ≫
            (Scheme.Etale.graphComplι e Wh).left :=
        Scheme.Hom.etale_map_left_comp_fst h _
      have hj' : (Scheme.Etale.graph (h ≫ e) W ≫ c.hom).left ≫
          pullback.fst (Scheme.Etale.graphTarget e Wh).hom h =
          (Scheme.Etale.graph h W).left ≫ pullback.fst Wh.hom h ≫
            (Scheme.Etale.graph e Wh).left := by
        rw [← hj, MorphismProperty.Comma.comp_left, Category.assoc, hpj.w]
      have hz : (Scheme.Etale.graphComplι e Wh).left
          ((pullback.fst (Scheme.Etale.graphComplObj e Wh).hom h) x) =
          (Scheme.Etale.graph e Wh).left y := by
        change ((Scheme.Etale.graph (h ≫ e) W ≫ c.hom).left ≫
          pullback.fst (Scheme.Etale.graphTarget e Wh).hom h) y =
          ((l ≫ c.inv ≫ c.hom).left ≫
            pullback.fst (Scheme.Etale.graphTarget e Wh).hom h) x at hy'
        rw [c.inv_hom_id, Category.comp_id, hl, hj',
          Scheme.Etale.graph_left_fst_assoc] at hy'
        exact hy'.symm
      exact Set.disjoint_left.mp (Scheme.Etale.isCompl_range_graph e Wh).disjoint
        ⟨y, hz.symm⟩ ⟨_, rfl⟩
  rw [← Category.assoc, heq, Category.assoc, lowerStarComp_hom_app_hom_app,
    ← Functor.map_comp, ← op_comp]
  congr 2
  change _ = ((h ≫ e).Etale.map _).op
  simp only [c, Iso.trans_inv, Iso.app_inv, Functor.mapIso_inv, op_comp]
  rw [Category.assoc]
  change _ ≫ (((MorphismProperty.Over.pullbackComp (P := @Etale)
    (Q := ⊤) h e).inv.app Whe).op ≫
    ((MorphismProperty.Over.pullbackComp (P := @Etale)
      (Q := ⊤) h e).hom.app Whe).op) = _
  rw [← op_comp]
  simp

set_option backward.isDefEq.respectTransparency false in
/-- The composition determined inside direct image sends a pair of etale lifts to their
composite lift.
Source: Stacks Project, Tags 0F4Y and 0F50
(blueprint: lem-sfb-etale-support-nested-summands).

Proof: postcompose the two arrows with the injective support inclusion on the final
etale test object. Substitute the three sum-to-direct-image normalization equations and
the section-preserving equation of sigma. The adjunction units select the summands
indexed by the structural lifts. Extending first along the inner graph and then along
the outer graph gives the extension along the composite graph: the sections agree on
that graph and are zero on its clopen complement. Two applications of graph/complement
sheaf extensionality prove equality directly. The mapComp inverse is the
canonical identification of the two composite test objects. Injectivity cancels the
postcomposition and proves the claimed equation. -/
theorem etaleSupportNestedSummands
    (A : Type (u + 1)) [CommRing A]
    {V T B : Scheme.{u}} (h : V ⟶ T) (e : T ⟶ B) [Etale h] [Etale e]
    [IsSeparated h] [IsSeparated e]
    (F : Sheaf V.smallEtaleTopology (ModuleCat.{u + 1} A) ⥤
      Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} A))
    (G : Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} A) ⥤
      Sheaf B.smallEtaleTopology (ModuleCat.{u + 1} A))
    (H : Sheaf V.smallEtaleTopology (ModuleCat.{u + 1} A) ⥤
      Sheaf B.smallEtaleTopology (ModuleCat.{u + 1} A))
    (ιh : F ⟶ lowerStar (ModuleCat.{u + 1} A) h)
    (ιe : G ⟶ lowerStar (ModuleCat.{u + 1} A) e)
    (ιhe : H ⟶ lowerStar (ModuleCat.{u + 1} A) (h ≫ e))
    (hi : ∀ (M : Sheaf V.smallEtaleTopology (ModuleCat.{u + 1} A)) (W : B.Etale),
      Function.Injective ((ιhe.app M).hom.app (Opposite.op W)))
    (oh : etaleLowerShriek (ModuleCat.{u + 1} A) h inferInstance ≅ F)
    (oe : etaleLowerShriek (ModuleCat.{u + 1} A) e inferInstance ≅ G)
    (ohe : etaleLowerShriek (ModuleCat.{u + 1} A) (h ≫ e) inferInstance ≅ H)
    (nh : ∀ M, oh.hom.app M ≫ ιh.app M =
      etaleLowerShriekToLowerStar (ModuleCat.{u + 1} A) h M)
    (ne : ∀ M, oe.hom.app M ≫ ιe.app M =
      etaleLowerShriekToLowerStar (ModuleCat.{u + 1} A) e M)
    (nhe : ∀ M, ohe.hom.app M ≫ ιhe.app M =
      etaleLowerShriekToLowerStar (ModuleCat.{u + 1} A) (h ≫ e) M)
    (σ : F ⋙ G ≅ H)
    (nσ : ∀ M, σ.hom.app M ≫ ιhe.app M =
      ιe.app (F.obj M) ≫ (lowerStar (ModuleCat.{u + 1} A) e).map (ιh.app M) ≫
        (lowerStarComp (ModuleCat.{u + 1} A) h e).hom.app M)
    (M : Sheaf V.smallEtaleTopology (ModuleCat.{u + 1} A)) (W : V.Etale) :
          ((etaleLowerShriekRestrictionAdjunction (ModuleCat.{u + 1} A) h).unit.app M).hom.app
              (Opposite.op W) ≫
            (oh.hom.app M).hom.app
              (Opposite.op ((MorphismProperty.Over.map ⊤ (inferInstance : Etale h)).obj W)) ≫
            ((etaleLowerShriekRestrictionAdjunction (ModuleCat.{u + 1} A) e).unit.app
              (F.obj M)).hom.app
              (Opposite.op ((MorphismProperty.Over.map ⊤ (inferInstance : Etale h)).obj W)) ≫
            (oe.hom.app (F.obj M)).hom.app
              (Opposite.op ((MorphismProperty.Over.map ⊤ (inferInstance : Etale e)).obj
                ((MorphismProperty.Over.map ⊤ (inferInstance : Etale h)).obj W))) ≫
            (σ.hom.app M).hom.app
              (Opposite.op ((MorphismProperty.Over.map ⊤ (inferInstance : Etale e)).obj
                ((MorphismProperty.Over.map ⊤ (inferInstance : Etale h)).obj W))) =
          ((etaleLowerShriekRestrictionAdjunction (ModuleCat.{u + 1} A)
              (h ≫ e)).unit.app M).hom.app (Opposite.op W) ≫
            (ohe.hom.app M).hom.app
              (Opposite.op
                ((MorphismProperty.Over.map ⊤ (inferInstance : Etale (h ≫ e))).obj W)) ≫
            (H.obj M).obj.map
              ((MorphismProperty.Over.mapComp ⊤ (inferInstance : Etale h)
                (inferInstance : Etale e)).inv.app W).op := by
  let Wh : T.Etale := (MorphismProperty.Over.map ⊤ (inferInstance : Etale h)).obj W
  let Whe : B.Etale := (MorphismProperty.Over.map ⊤ (inferInstance : Etale e)).obj Wh
  let q := (MorphismProperty.Over.mapComp ⊤
    (inferInstance : Etale h) (inferInstance : Etale e)).inv.app W
  have hm : Mono ((ιhe.app M).hom.app (Opposite.op Whe)) :=
    ConcreteCategory.mono_of_injective _ (hi M Whe)
  apply (cancel_mono ((ιhe.app M).hom.app (Opposite.op Whe))).mp
  have hs := congrArg (fun k => k.hom.app (Opposite.op Whe)) (nσ M)
  change (σ.hom.app M).hom.app (Opposite.op Whe) ≫
    (ιhe.app M).hom.app (Opposite.op Whe) =
    (ιe.app (F.obj M)).hom.app (Opposite.op Whe) ≫
      ((lowerStar (ModuleCat.{u + 1} A) e).map (ιh.app M)).hom.app (Opposite.op Whe) ≫
      ((lowerStarComp (ModuleCat.{u + 1} A) h e).hom.app M).hom.app
        (Opposite.op Whe) at hs
  have he := unit_comp_normalized_inclusion A e G ιe oe (F.obj M) (ne (F.obj M)) Wh
  have hh := unit_comp_normalized_inclusion A h F ιh oh M (nh M) W
  have hc := unit_comp_normalized_inclusion A (h ≫ e) H ιhe ohe M (nhe M) W
  have hn := (ιhe.app M).hom.naturality q.op
  change (H.obj M).obj.map q.op ≫ (ιhe.app M).hom.app (Opposite.op Whe) =
    (ιhe.app M).hom.app (Opposite.op _) ≫
      ((lowerStar (ModuleCat.{u + 1} A) (h ≫ e)).obj M).obj.map q.op at hn
  simp only [Category.assoc]
  rw [hs, hn]
  rw [reassoc_of% he, lowerStar_map_hom_app]
  erw [← reassoc_of% (Scheme.Etale.graphExtend_natural e (ιh.app M) Wh)]
  rw [reassoc_of% hh, reassoc_of% hc]
  exact graphExtend_comp A h e M W

end AlgebraicGeometry.Etale
