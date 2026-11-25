/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.Etale.LowerShriek.BaseChange
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.FiniteEtale
import WeilConjectures.SixFunctors.BaseChange.Etale
import WeilConjectures.SixFunctors.Etale.SmoothBaseChange.DegreeZero

/-! # The sheaf sum mate in the common direct image

Source: Stacks Project, Tags 0F4L, 0F7B and 0F7F.
-/

@[expose] public section

set_option autoImplicit false
set_option backward.defeqAttrib.useBackward true
universe u
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.Etale

attribute [local irreducible] upperStar etaleLowerShriek

private theorem sum_mate_unit
    {C D E F : Type*} [Category C] [Category D] [Category E] [Category F]
    {L : C ⥤ D} {R : D ⥤ C} {P : D ⥤ E} {S : E ⥤ D}
    {Q : C ⥤ F} {T : F ⥤ C} {V : F ⥤ E} {W : E ⥤ F}
    (a : L ⊣ R) (b : P ⊣ S) (c : Q ⊣ T) (d : V ⊣ W)
    (x : S ⋙ R ≅ W ⋙ T) (M : F) :
    let e := (((a.comp b).ofNatIsoRight x).leftAdjointUniq (c.comp d)).hom
    let θ := (mateEquiv c b (TwoSquare.mk _ _ _ _ e))
    a.unit.app (T.obj M) ≫ R.map (θ.app M) ≫ x.hom.app (V.obj M) =
      T.map (d.unit.app M) := by
  dsimp only
  have h := Adjunction.unit_leftAdjointUniq_hom_app
    ((a.comp b).ofNatIsoRight x) (c.comp d) (T.obj M)
  simp only [Adjunction.ofNatIsoRight_unit, Adjunction.comp_unit_app,
    NatTrans.comp_app, Functor.whiskerLeft_app, Functor.comp_map,
    Functor.comp_obj] at h
  simp only [Category.assoc] at h
  have hn := x.hom.naturality
    ((((a.comp b).ofNatIsoRight x).leftAdjointUniq (c.comp d)).hom.app (T.obj M))
  simp only [Functor.comp_map, Functor.comp_obj] at hn
  rw [← hn] at h
  have h' := congrArg (fun z ↦ z ≫ T.map (W.map (V.map (c.counit.app M)))) h
  simp only [Category.assoc] at h'
  have hn' := x.hom.naturality (V.map (c.counit.app M))
  simp only [Functor.comp_map, Functor.comp_obj, Functor.id_obj] at hn'
  rw [← hn'] at h'
  have hd := d.unit.naturality (c.counit.app M)
  simp only [Functor.comp_map, Functor.id_map, Functor.comp_obj, Functor.id_obj] at hd
  rw [← T.map_comp, ← hd, T.map_comp] at h'
  rw [c.right_triangle_components_assoc] at h'
  simp only [mateEquiv, Equiv.coe_fn_mk, NatTrans.comp_app,
    Functor.rightUnitor_inv_app, Functor.whiskerLeft_app,
    Functor.associator_hom_app, Functor.associator_inv_app,
    Functor.whiskerRight_app, Functor.comp_map, Functor.leftUnitor_hom_app,
    Category.id_comp, Category.comp_id, Functor.map_comp,
    Functor.comp_obj, Functor.id_obj, TwoSquare.mk]
  simpa only [Category.assoc] using h'

private theorem sum_comparison_unit
    (A : Type (u + 1)) [CommRing A]
    {X Y : Scheme.{u}} (f : X ⟶ Y) [Etale f] [IsSeparated f]
    (G : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A)) :
    (etaleLowerShriekUpperStarAdjunction (ModuleCat.{u + 1} A) f inferInstance).unit.app G ≫
      (upperStar (ModuleCat.{u + 1} A) f).map
        (etaleLowerShriekToLowerStar (ModuleCat.{u + 1} A) f G) ≫
      (upperStarIsoLocalizationRestriction (ModuleCat.{u + 1} A) f inferInstance).hom.app
        ((lowerStar (ModuleCat.{u + 1} A) f).obj G) =
      (lowerStarUnit (ModuleCat.{u + 1} A) f).app G := by
  have h := ((etaleLowerShriekRestrictionAdjunction (ModuleCat.{u + 1} A) f).homEquiv
    G ((lowerStar (ModuleCat.{u + 1} A) f).obj G)).apply_symm_apply
      ((lowerStarUnit (ModuleCat.{u + 1} A) f).app G)
  change (etaleLowerShriekRestrictionAdjunction (ModuleCat.{u + 1} A) f).homEquiv _ _
    (etaleLowerShriekToLowerStar (ModuleCat.{u + 1} A) f G) = _ at h
  rw [Adjunction.homEquiv_unit] at h
  simp only [etaleLowerShriekRestrictionAdjunction, Adjunction.ofNatIsoRight_unit,
    NatTrans.comp_app, Functor.whiskerLeft_app] at h
  rw [Category.assoc, ← (upperStarIsoLocalizationRestriction
    (ModuleCat.{u + 1} A) f inferInstance).hom.naturality] at h
  exact h

private theorem graphExtend_zero_of_disjoint
    (A : Type (u + 1)) [CommRing A]
    {X Y : Scheme.{u}} (f : X ⟶ Y) [Etale f] [IsSeparated f]
    (G : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A))
    (U V : X.Etale) (k : V ⟶ Scheme.Etale.graphTarget f U)
    (hk : Disjoint (Set.range k.left) (Set.range (Scheme.Etale.graph f U).left)) :
    Scheme.Etale.graphExtend f G U ≫ G.obj.map k.op = 0 := by
  let l : V ⟶ Scheme.Etale.graphComplObj f U :=
    MorphismProperty.Over.homMk
      (IsOpenImmersion.lift (Scheme.Etale.graphComplι f U).left k.left (by
        change Set.range k.left ⊆ Set.range (Scheme.Etale.graphCompl f U).ι
        rw [Scheme.Opens.range_ι]
        exact Set.disjoint_left.mp hk))
      (by
        change _ ≫ (Scheme.Etale.graphComplι f U).left ≫ _ = _
        rw [← Category.assoc, IsOpenImmersion.lift_fac]
        exact k.w) trivial
  have hl : l ≫ Scheme.Etale.graphComplι f U = k :=
    MorphismProperty.Over.Hom.ext (IsOpenImmersion.lift_fac _ _ _)
  rw [← hl, op_comp, Functor.map_comp,
    Scheme.Etale.graphExtend_graphComplι_assoc, zero_comp]

private theorem graph_unit_exchange
    (A : Type (u + 1)) [CommRing A]
    {W Y' Z Y : Scheme.{u}} (q : W ⟶ Y') (p : Z ⟶ Y)
    (b : W ⟶ Z) [Etale b] [IsSeparated b]
    (v : Y' ⟶ Y) [Etale v] [IsSeparated v]
    (sq : IsPullback b q p v)
    (F : Sheaf W.smallEtaleTopology (ModuleCat.{u + 1} A)) :
    (lowerStarUnit (ModuleCat.{u + 1} A) v).app
        ((lowerStar (ModuleCat.{u + 1} A) q).obj F) ≫
      (localizationRestriction (ModuleCat.{u + 1} A) v inferInstance).map
        ((squareLowerStarIso (ModuleCat.{u + 1} A) sq.toCommSq.flip).hom.app F) ≫
      (localizationRestrictionBaseChangeMap (ModuleCat.{u + 1} A) sq.toCommSq.flip).app
        ((lowerStar (ModuleCat.{u + 1} A) b).obj F) =
      (lowerStar (ModuleCat.{u + 1} A) q).map
        ((lowerStarUnit (ModuleCat.{u + 1} A) b).app F) := by
  ext ⟨U⟩ : 3
  change Scheme.Etale.graphExtend v ((lowerStar (ModuleCat.{u + 1} A) q).obj F) U ≫
      ((squareLowerStarIso (ModuleCat.{u + 1} A) sq.toCommSq.flip).hom.app F).hom.app
        (Opposite.op ((MorphismProperty.Over.map ⊤ (inferInstance : Etale v)).obj U)) ≫
      F.obj.map ((MorphismProperty.Over.pullback @Etale ⊤ b).map
        ((MorphismProperty.Over.pullbackMapComparison (inferInstance : Etale v)
          (inferInstance : Etale b) sq.toCommSq.flip).app U)).op =
    Scheme.Etale.graphExtend b F ((MorphismProperty.Over.pullback @Etale ⊤ q).obj U)
  simp only [squareLowerStarIso, Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app,
    ObjectProperty.FullSubcategory.comp_hom, lowerStarComp,
    Functor.sheafPushforwardContinuousComp'_hom_app_hom_app,
    Functor.sheafPushforwardContinuousComp'_inv_app_hom_app]
  simp only [Iso.symm_inv, ← Functor.map_comp, ← op_comp]
  let Uq := q.Etale.obj U
  let C : Scheme.Etale.graphTarget b Uq ≅
      q.Etale.obj (Scheme.Etale.graphTarget v U) :=
    haveI := MorphismProperty.Over.isIso_pullbackMapComparison_of_isPullback
      (inferInstance : Etale v) (inferInstance : Etale b) sq.flip
    (b.Etale.mapIso (asIso ((MorphismProperty.Over.pullbackMapComparison
      (inferInstance : Etale v) (inferInstance : Etale b) sq.toCommSq.flip).app U))) ≪≫
      ((MorphismProperty.Over.pullbackComp (P := @Etale) (Q := ⊤)
        b p (q ≫ v) sq.w.symm).app
          ((MorphismProperty.Over.map ⊤ (inferInstance : Etale v)).obj U)).symm ≪≫
      (MorphismProperty.Over.pullbackComp (P := @Etale) (Q := ⊤) q v).app
        ((MorphismProperty.Over.map ⊤ (inferInstance : Etale v)).obj U)
  let j := q.Etale.map (Scheme.Etale.graph v U)
  let l := q.Etale.map (Scheme.Etale.graphComplι v U)
  have hj : Scheme.Etale.graph b Uq ≫ C.hom = j := by
    apply MorphismProperty.Over.Hom.ext
    change (Scheme.Etale.graph b Uq).left ≫
        (b.Etale.map ((MorphismProperty.Over.pullbackMapComparison
          (inferInstance : Etale v) (inferInstance : Etale b) sq.toCommSq.flip).app U)).left ≫
        ((MorphismProperty.Over.pullbackComp (P := @Etale) (Q := ⊤)
          b p (q ≫ v) sq.w.symm).inv.app
            ((MorphismProperty.Over.map ⊤ (inferInstance : Etale v)).obj U)).left ≫
        ((MorphismProperty.Over.pullbackComp (P := @Etale) (Q := ⊤) q v).hom.app
          ((MorphismProperty.Over.map ⊤ (inferInstance : Etale v)).obj U)).left = j.left
    apply pullback.hom_ext
    · apply pullback.hom_ext <;>
        simp [Category.assoc, Uq, j, Scheme.Etale.graph_left,
          MorphismProperty.Over.pullbackComp_hom_app_left,
          MorphismProperty.Over.pullbackComp_inv_app_left,
          MorphismProperty.Over.pullbackMapComparison_app_left,
          Scheme.Hom.Etale, MorphismProperty.Over.pullback,
          Scheme.Etale.graphTarget, MorphismProperty.Over.mk, pullback.condition]
    · simp [Category.assoc, Uq, j, Scheme.Etale.graph_left,
        MorphismProperty.Over.pullbackComp_hom_app_left,
        MorphismProperty.Over.pullbackComp_inv_app_left,
        MorphismProperty.Over.pullbackMapComparison_app_left,
        Scheme.Hom.Etale, MorphismProperty.Over.pullback,
        Scheme.Etale.graphTarget, MorphismProperty.Over.mk]
  have heq : Scheme.Etale.graphExtend v ((lowerStar (ModuleCat.{u + 1} A) q).obj F) U =
      Scheme.Etale.graphExtend b F Uq ≫ F.obj.map C.inv.op := by
    apply Scheme.Etale.graph_hom_ext v ((lowerStar (ModuleCat.{u + 1} A) q).obj F)
    · change _ ≫ F.obj.map j.op = _ ≫ F.obj.map j.op
      have hg := Scheme.Etale.graphExtend_graph v
        ((lowerStar (ModuleCat.{u + 1} A) q).obj F) U
      change Scheme.Etale.graphExtend v ((lowerStar (ModuleCat.{u + 1} A) q).obj F) U ≫
        F.obj.map j.op = 𝟙 _ at hg
      rw [hg]
      simp only [Category.assoc, ← Functor.map_comp, ← op_comp]
      have hji : j ≫ C.inv = Scheme.Etale.graph b Uq := by
        rw [← hj, Category.assoc, C.hom_inv_id, Category.comp_id]
      rw [hji, Scheme.Etale.graphExtend_graph]
      rfl
    · change _ ≫ F.obj.map l.op = _ ≫ F.obj.map l.op
      have hg := Scheme.Etale.graphExtend_graphComplι v
        ((lowerStar (ModuleCat.{u + 1} A) q).obj F) U
      change Scheme.Etale.graphExtend v ((lowerStar (ModuleCat.{u + 1} A) q).obj F) U ≫
        F.obj.map l.op = 0 at hg
      rw [hg]
      simp only [Category.assoc, ← Functor.map_comp, ← op_comp]
      symm
      apply graphExtend_zero_of_disjoint A b F Uq _ (l ≫ C.inv)
      apply Set.disjoint_left.mpr
      rintro _ ⟨x, rfl⟩ ⟨y, hy⟩
      have hy' := congrArg (fun z ↦
        (pullback.fst (Scheme.Etale.graphTarget v U).hom q) (C.hom.left z)) hy
      have hl : l.left ≫ pullback.fst (Scheme.Etale.graphTarget v U).hom q =
          pullback.fst (Scheme.Etale.graphComplObj v U).hom q ≫
            (Scheme.Etale.graphComplι v U).left :=
        Scheme.Hom.etale_map_left_comp_fst q _
      have hj' : j.left ≫ pullback.fst (Scheme.Etale.graphTarget v U).hom q =
          pullback.fst U.hom q ≫ (Scheme.Etale.graph v U).left :=
        Scheme.Hom.etale_map_left_comp_fst q _
      change ((Scheme.Etale.graph b Uq ≫ C.hom).left ≫
        pullback.fst (Scheme.Etale.graphTarget v U).hom q) y =
        ((l ≫ C.inv ≫ C.hom).left ≫
          pullback.fst (Scheme.Etale.graphTarget v U).hom q) x at hy'
      rw [C.inv_hom_id, Category.comp_id, hl, hj, hj'] at hy'
      exact Set.disjoint_left.mp (Scheme.Etale.isCompl_range_graph v U).disjoint
        ⟨_, hy'⟩ ⟨_, rfl⟩
  change Scheme.Etale.graphExtend v ((lowerStar (ModuleCat.{u + 1} A) q).obj F) U ≫
    F.obj.map C.hom.op = Scheme.Etale.graphExtend b F Uq
  rw [heq, Category.assoc, ← F.obj.map_comp, ← op_comp,
    C.hom_inv_id, op_id, F.obj.map_id, Category.comp_id]

/-- The sheaf mate of Cartesian sum base change preserves its underlying section.
Source: Stacks Project, Tags 0F4L, 0F7B and 0F7F
(blueprint: lem-pur-cartesian-sum-mate-sheaf-normalization).

Proof in words: transpose the equation under the sum/restriction adjunction for v.
The graph extension defining etaleLowerShriekToLowerStar is identity on the graph
of a lifted etale section and zero on its clopen complement. The Cartesian
base-change isomorphism, defined by uniqueness of the composed left adjoints,
transports its unit to the unit for the corresponding pulled-back lifted section.
Consequently the forward mate along q* ⊣ q_* and p* ⊣ p_* carries that graph
extension to the same underlying section over W times_Y the test object. On
the complement both composites are zero. Apply graph_hom_ext to these two
restrictions; naturality of the direct-image composition comparisons identifies
both ordinary direct images with the one along b followed by p. Sheafification
and the injective adjunction Hom bijection give the equation for every sheaf F.
Only a Cartesian square and separated etale horizontal arrows are used; neither
properness nor any derived category or coefficient finiteness is needed. For an
empty graph both restrictions vanish, and for identity squares this is the
triangle identity of the sum/restriction adjunction. -/
theorem cartesian_sum_mate_sheaf_normalization
    (A : Type (u + 1)) [CommRing A]
    {W Y' Z Y : Scheme.{u}}
    (q : W ⟶ Y') (p : Z ⟶ Y)
    (b : W ⟶ Z) [Etale b] [IsSeparated b]
    (v : Y' ⟶ Y) [Etale v] [IsSeparated v]
    (sq : IsPullback b q p v) :
    let θ := (mateEquiv
      (upperStarLowerStarAdjunction (ModuleCat.{u + 1} A) q)
      (upperStarLowerStarAdjunction (ModuleCat.{u + 1} A) p)
      (TwoSquare.mk _ _ _ _ (etaleLowerShriekBaseChangeIso A sq).hom))
    (∀ F : Sheaf W.smallEtaleTopology (ModuleCat.{u + 1} A),
      θ.app F ≫
          (lowerStar (ModuleCat.{u + 1} A) p).map
            (etaleLowerShriekToLowerStar (ModuleCat.{u + 1} A) b F) ≫
          (lowerStarComp (ModuleCat.{u + 1} A) b p).hom.app F =
        etaleLowerShriekToLowerStar (ModuleCat.{u + 1} A) v
            ((lowerStar (ModuleCat.{u + 1} A) q).obj F) ≫
          (lowerStarComp (ModuleCat.{u + 1} A) q v (b ≫ p) sq.w).hom.app F) := by
  dsimp only
  intro F
  let a := etaleLowerShriekUpperStarAdjunction (ModuleCat.{u + 1} A) v inferInstance
  let d := etaleLowerShriekUpperStarAdjunction (ModuleCat.{u + 1} A) b inferInstance
  let x := baseChangeMap (ModuleCat.{u + 1} A) sq.toCommSq
  have hxapp : ∀ G, IsIso (x.app G) := fun G ↦
    isIso_baseChangeMap_app_of_flat A sq G
  have hx : IsIso x := NatIso.isIso_of_isIso_app x
  let θ := (mateEquiv (upperStarLowerStarAdjunction (ModuleCat.{u + 1} A) q)
    (upperStarLowerStarAdjunction (ModuleCat.{u + 1} A) p)
    (TwoSquare.mk _ _ _ _ (etaleLowerShriekBaseChangeIso A sq).hom))
  have hu : a.unit.app ((lowerStar (ModuleCat.{u + 1} A) q).obj F) ≫
      (upperStar (ModuleCat.{u + 1} A) v).map (θ.app F) ≫
      x.app ((etaleLowerShriek (ModuleCat.{u + 1} A) b inferInstance).obj F) =
      (lowerStar (ModuleCat.{u + 1} A) q).map (d.unit.app F) := by
    exact sum_mate_unit a (upperStarLowerStarAdjunction (ModuleCat.{u + 1} A) p)
      (upperStarLowerStarAdjunction (ModuleCat.{u + 1} A) q) d (asIso x) F
  have hg : a.unit.app ((lowerStar (ModuleCat.{u + 1} A) q).obj F) ≫
      (upperStar (ModuleCat.{u + 1} A) v).map
        (etaleLowerShriekToLowerStar (ModuleCat.{u + 1} A) v
            ((lowerStar (ModuleCat.{u + 1} A) q).obj F) ≫
          (squareLowerStarIso (ModuleCat.{u + 1} A) sq.toCommSq.flip).hom.app F) ≫
      x.app ((lowerStar (ModuleCat.{u + 1} A) b).obj F) =
      (lowerStar (ModuleCat.{u + 1} A) q).map
        (d.unit.app F ≫ (upperStar (ModuleCat.{u + 1} A) b).map
          (etaleLowerShriekToLowerStar (ModuleCat.{u + 1} A) b F)) := by
    have hbc := baseChangeMap_flip_eq (ModuleCat.{u + 1} A) sq.toCommSq.flip
    change x = _ at hbc
    rw [hbc]
    simp only [NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app,
      Functor.map_comp, Category.assoc]
    have hn := (upperStarIsoLocalizationRestriction (ModuleCat.{u + 1} A)
      v inferInstance).hom.naturality
        ((squareLowerStarIso (ModuleCat.{u + 1} A) sq.toCommSq.flip).hom.app F)
    simp only [Functor.comp_obj] at hn
    erw [reassoc_of% hn]
    rw [reassoc_of% (sum_comparison_unit A v ((lowerStar (ModuleCat.{u + 1} A) q).obj F))]
    rw [reassoc_of% (graph_unit_exchange A q p b v sq F)]
    rw [← Functor.map_comp, ← Functor.map_comp]
    apply congrArg ((lowerStar (ModuleCat.{u + 1} A) q).map)
    have hb := congrArg (fun z ↦ z ≫
      (upperStarIsoLocalizationRestriction (ModuleCat.{u + 1} A)
        b inferInstance).inv.app ((lowerStar (ModuleCat.{u + 1} A) b).obj F))
      (sum_comparison_unit A b F)
    simp only [Category.assoc, Iso.hom_inv_id_app, Category.comp_id] at hb
    exact hb.symm
  suffices hmain : θ.app F ≫ (lowerStar (ModuleCat.{u + 1} A) p).map
        (etaleLowerShriekToLowerStar (ModuleCat.{u + 1} A) b F) =
      etaleLowerShriekToLowerStar (ModuleCat.{u + 1} A) v
          ((lowerStar (ModuleCat.{u + 1} A) q).obj F) ≫
        (squareLowerStarIso (ModuleCat.{u + 1} A) sq.toCommSq.flip).hom.app F by
    rw [← Category.assoc, hmain, Category.assoc, squareLowerStarIso_eq]
    simp only [Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app, Category.assoc]
    erw [Iso.inv_hom_id_app, Category.comp_id]
  apply (a.homEquiv ((lowerStar (ModuleCat.{u + 1} A) q).obj F)
    ((lowerStar (ModuleCat.{u + 1} A) p).obj
      ((lowerStar (ModuleCat.{u + 1} A) b).obj F))).injective
  rw [Adjunction.homEquiv_unit, Adjunction.homEquiv_unit]
  have := hxapp ((lowerStar (ModuleCat.{u + 1} A) b).obj F)
  have hc :
      a.unit.app ((lowerStar (ModuleCat.{u + 1} A) q).obj F) ≫
        (upperStar (ModuleCat.{u + 1} A) v).map
          (θ.app F ≫ (lowerStar (ModuleCat.{u + 1} A) p).map
            (etaleLowerShriekToLowerStar (ModuleCat.{u + 1} A) b F)) ≫
        x.app ((lowerStar (ModuleCat.{u + 1} A) b).obj F) =
      a.unit.app ((lowerStar (ModuleCat.{u + 1} A) q).obj F) ≫
        (upperStar (ModuleCat.{u + 1} A) v).map
          (etaleLowerShriekToLowerStar (ModuleCat.{u + 1} A) v
            ((lowerStar (ModuleCat.{u + 1} A) q).obj F) ≫
            (squareLowerStarIso (ModuleCat.{u + 1} A) sq.toCommSq.flip).hom.app F) ≫
        x.app ((lowerStar (ModuleCat.{u + 1} A) b).obj F) := by
    simp only [Functor.map_comp, Category.assoc]
    have hn := x.naturality (etaleLowerShriekToLowerStar (ModuleCat.{u + 1} A) b F)
    simp only [Functor.comp_map] at hn
    erw [hn]
    erw [reassoc_of% hu]
    simpa only [Functor.map_comp, Category.assoc] using hg.symm
  have he := congrArg (fun z ↦ z ≫ inv
    (x.app ((lowerStar (ModuleCat.{u + 1} A) b).obj F))) hc
  simpa only [Category.assoc, IsIso.hom_inv_id, Category.comp_id] using he

end AlgebraicGeometry.Etale
