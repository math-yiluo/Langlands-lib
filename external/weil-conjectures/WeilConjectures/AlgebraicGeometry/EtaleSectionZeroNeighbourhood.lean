/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.Mathlib.AlgebraicGeometry.Sites.Etale
public import Mathlib.Algebra.Category.Grp.Basic
import WeilConjectures.Mathlib.AlgebraicGeometry.Sites.EtalePoint
import Mathlib.AlgebraicGeometry.Morphisms.UniversallyOpen

/-! # A zero neighbourhood for a section killed by inverse image

Source: Stacks Project, Tags 03PN (geometric stalks) and 03Q1 (pullback stalks).
(blueprint: lem-weil-pbc-etale-section-zero-neighbourhood)
-/

@[expose] public section

universe u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry TopologicalSpace

set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
private theorem etaleSection_zero_pointed_witness
    {X T : Scheme.{u + 1}} (V : X.Etale) (a : T ⟶ V.left)
    (p : T ⟶ X) (hp : a ≫ V.hom = p)
    (H : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1} ⥤
      Sheaf T.smallEtaleTopology AddCommGrpCat.{u + 1})
    (hH : H ⊣ p.Etale.sheafPushforwardContinuous
      AddCommGrpCat.{u + 1} X.smallEtaleTopology T.smallEtaleTopology)
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1})
    (s : F.obj.obj (op V))
    (hs : ((hH.unit.app F).hom.app (op V) ≫
      (H.obj F).obj.map (MorphismProperty.Over.homMk
        (A := Scheme.Etale.mk (𝟙 T)) (B := p.Etale.obj V)
        (pullback.lift a (𝟙 T) (by
          change a ≫ V.hom = 𝟙 T ≫ p
          rw [Category.id_comp]
          exact hp))
        (by exact pullback.lift_snd _ _ _)).op) s = 0) (t : T) :
    ∃ (W : X.Etale) (g : W ⟶ V) (w : W.left),
      g.left w = a t ∧ F.obj.map g.op s = 0 := by
  classical
  let := hH.isRightAdjoint
  let y := T.algClosurePoint t
  let Φ := Scheme.pointSmallEtale y
  let Ψ := Φ.comap p.Etale (Scheme.Hom.coverPreserving_etale p)
  let b : Scheme.Etale.mk (𝟙 T) ⟶ p.Etale.obj V :=
    MorphismProperty.Over.homMk
      (pullback.lift a (𝟙 T) (by
        change a ≫ V.hom = 𝟙 T ≫ p
        simpa only [Category.id_comp] using hp))
      (by exact pullback.lift_snd _ _ _)
  let y₀ : Φ.fiber.obj (Scheme.Etale.mk (𝟙 T)) := Over.homMk y
  let v : Ψ.fiber.obj V := Φ.fiber.map b y₀
  let adj := p.Etale.sheafAdjunctionContinuous AddCommGrpCat.{u + 1}
    X.smallEtaleTopology T.smallEtaleTopology
  let e := adj.leftAdjointUniq hH
  have hu := Adjunction.unit_leftAdjointUniq_hom_app adj hH F
  have huV := NatTrans.congr_app (Sheaf.hom_ext_iff.1 hu) (op V)
  change (adj.unit.app F).hom.app (op V) ≫
    (e.hom.app F).hom.app (op (p.Etale.obj V)) =
    (hH.unit.app F).hom.app (op V) at huV
  let c := Φ.sheafFiberComapIso p.Etale
    (Scheme.Hom.coverPreserving_etale p) AddCommGrpCat.{u + 1}
  have hg : Ψ.toPresheafFiber V v F.obj ≫ (c.hom.app F) ≫
      Φ.presheafFiber.map (e.hom.app F).hom =
      (hH.unit.app F).hom.app (op V) ≫
        (H.obj F).obj.map b.op ≫
          Φ.toPresheafFiber (Scheme.Etale.mk (𝟙 T)) y₀ (H.obj F).obj := by
    rw [← Category.assoc,
      GrothendieckTopology.Point.toPresheafFiber_sheafFiberComapIso_hom_app]
    rw [Category.assoc, GrothendieckTopology.Point.toPresheafFiber_naturality]
    rw [← Category.assoc, huV]
    rw [GrothendieckTopology.Point.toPresheafFiber_w]
  have hz : Ψ.toPresheafFiber V v F.obj s = 0 := by
    apply (ConcreteCategory.bijective_of_isIso
      ((c.hom.app F) ≫ Φ.presheafFiber.map (e.hom.app F).hom)).1
    have he := congrArg (fun k ↦ k s) hg
    have hr : ((hH.unit.app F).hom.app (op V) ≫
        (H.obj F).obj.map b.op ≫
          Φ.toPresheafFiber (Scheme.Etale.mk (𝟙 T)) y₀ (H.obj F).obj) s = 0 := by
      rw [← Category.assoc, AddCommGrpCat.comp_apply]
      rw [show ((hH.unit.app F).hom.app (op V) ≫
        (H.obj F).obj.map b.op) s = 0 from hs]
      exact map_zero _
    change (Φ.presheafFiber.map (e.hom.app F).hom)
      ((c.hom.app F) (Ψ.toPresheafFiber V v F.obj s)) =
      (Φ.presheafFiber.map (e.hom.app F).hom) ((c.hom.app F) 0)
    rw [map_zero, map_zero]
    exact he.trans hr
  have heq : Ψ.toPresheafFiber V v F.obj s =
      Ψ.toPresheafFiber V v F.obj 0 := by simpa only [map_zero] using hz
  obtain ⟨W, g, w, hw, hzero⟩ := (Ψ.toPresheafFiber_eq_iff' V v s 0).mp heq
  let z : W.left := pullback.fst W.hom p
    (w.left (default : Spec (.of (AlgebraicClosure (T.residueField t)))))
  refine ⟨W, g, z, ?_, ?_⟩
  · have hw' := congrArg (fun k ↦ k.left ≫ pullback.fst V.hom p) hw
    change w.left ≫ (p.Etale.map g).left ≫ pullback.fst V.hom p =
      y ≫ b.left ≫ pullback.fst V.hom p at hw'
    rw [Scheme.Hom.etale_map_left_comp_fst,
      show b.left ≫ pullback.fst V.hom p = a from pullback.lift_fst _ _ _] at hw'
    have he := congrArg (fun k ↦ k (default : Spec (.of (AlgebraicClosure (T.residueField t))))) hw'
    change g.left (pullback.fst W.hom p
      (w.left (default : Spec (.of (AlgebraicClosure (T.residueField t)))))) = a t
    change g.left (pullback.fst W.hom p
      (w.left (default : Spec (.of (AlgebraicClosure (T.residueField t)))))) =
        a (y (default : Spec (.of (AlgebraicClosure (T.residueField t))))) at he
    simpa only [y, Scheme.algClosurePoint_base] using he
  · simpa only [map_zero] using hzero

set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
/-- If a section on an étale object becomes zero on a scheme mapping to that object,
then it is zero on an open neighbourhood of the image.
Source: Stacks Project, Tag 03PN, Definition 59.29.6 (filtered-colimit stalks),
and Tag 03Q1, lemma-stalk-pullback (3), including compatibility with the unit.
Proof: The zero locus of a section is open: a zero geometric germ is represented by
an étale neighbourhood of the given pointed object on which the section is zero,
by equality detection in the filtered colimit defining its stalk. The image of this neighbourhood
is open, and the neighbourhood covers its image. Sheaf separatedness therefore makes
the section zero on that image. Take the union of all opens on which the section is
zero. Sheaf separatedness on this open covering makes the section zero on the union.
For each point of T choose a geometric point above it. The inverse-image stalk
isomorphism, with its unit-germ compatibility and naturality for restriction,
carries the germ of the displayed canonical section to the original germ
on V. Its vanishing puts the image point in the zero locus. The uniqueness isomorphism
between H and the standard inverse image preserves the units, so the same reasoning
applies to the supplied adjunction. The empty scheme has empty image and permits the
empty open; for the zero section the whole object is a zero neighbourhood.
(blueprint: lem-weil-pbc-etale-section-zero-neighbourhood) -/
theorem etaleSection_zero_neighbourhood
    {X T : Scheme.{u + 1}} (V : X.Etale) (a : T ⟶ V.left)
    (p : T ⟶ X) (hp : a ≫ V.hom = p)
    (H : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1} ⥤
      Sheaf T.smallEtaleTopology AddCommGrpCat.{u + 1})
    (hH : H ⊣ p.Etale.sheafPushforwardContinuous
      AddCommGrpCat.{u + 1} X.smallEtaleTopology T.smallEtaleTopology)
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1})
    (s : F.obj.obj (op V))
    (hs : ((hH.unit.app F).hom.app (op V) ≫
      (H.obj F).obj.map (MorphismProperty.Over.homMk
        (A := Scheme.Etale.mk (𝟙 T)) (B := p.Etale.obj V)
        (pullback.lift a (𝟙 T) (by
          change a ≫ V.hom = 𝟙 T ≫ p
          rw [Category.id_comp]
          exact hp))
        (by exact pullback.lift_snd _ _ _)).op) s = 0) :
    ∃ (U : V.left.Opens), Set.range a ⊆ (U : Set V.left) ∧
      F.obj.map (MorphismProperty.Over.homMk
        (A := Scheme.Etale.mk (U.ι ≫ V.hom)) (B := V) U.ι rfl).op s = 0 := by
  classical
  choose W g w hw hz using etaleSection_zero_pointed_witness V a p hp H hH F s hs
  let O : T → V.left.Opens := fun t ↦
    ⟨Set.range (g t).left, (g t).left.isOpenMap.isOpen_range⟩
  let U : V.left.Opens := ⨆ t, O t
  let B : X.Etale := Scheme.Etale.mk (U.ι ≫ V.hom)
  let j : B ⟶ V := MorphismProperty.Over.homMk U.ι rfl
  have hU (t : T) : Set.range (g t).left ⊆ (U : Set V.left) :=
    show O t ≤ U from le_iSup O t
  let q (t : T) : (W t).left ⟶ U.toScheme :=
    IsOpenImmersion.lift U.ι (g t).left (by rw [Scheme.Opens.range_ι]; exact hU t)
  have hq (t : T) : q t ≫ U.ι = (g t).left := IsOpenImmersion.lift_fac _ _ _
  let q' (t : T) : W t ⟶ B :=
    MorphismProperty.Over.homMk (q t) (by
      change q t ≫ U.ι ≫ V.hom = (W t).hom
      rw [← Category.assoc, hq, MorphismProperty.Over.w])
  have hfac (t : T) : q' t ≫ j = g t := by
    apply MorphismProperty.Over.Hom.ext
    exact hq t
  have hcover : Sieve.ofArrows W q' ∈ X.smallEtaleTopology B := by
    rw [Scheme.ofArrows_mem_smallEtaleTopology_iff]
    apply Set.eq_univ_of_forall
    intro x
    have hx : x.val ∈ (U : Set V.left) := x.property
    change x.val ∈ (⨆ t, O t : V.left.Opens) at hx
    simp only [Opens.mem_iSup] at hx
    obtain ⟨t, z, hz⟩ := hx
    refine Set.mem_iUnion.mpr ⟨t, z, ?_⟩
    apply Subtype.ext
    exact (congrArg (fun k : (W t).left ⟶ V.left ↦ k z) (hq t)).trans hz
  refine ⟨U, ?_, ?_⟩
  · rintro _ ⟨t, rfl⟩
    exact hU t ⟨w t, hw t⟩
  · change F.obj.map j.op s = 0
    apply F.isSeparated B _ hcover
    intro Y f hf
    obtain ⟨Z, k, l, ⟨t⟩, rfl⟩ := hf
    rw [map_zero]
    have he : F.obj.map (q' t).op (F.obj.map j.op s) = 0 := by
      change (F.obj.map j.op ≫ F.obj.map (q' t).op) s = 0
      rw [← Functor.map_comp, ← op_comp, hfac]
      exact hz t
    rw [op_comp, Functor.map_comp, AddCommGrpCat.comp_apply, he, map_zero]

