/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.Mathlib.AlgebraicGeometry.Sites.Etale
public import Mathlib.Algebra.Category.Grp.Basic
import WeilConjectures.Mathlib.AlgebraicGeometry.Sites.EtalePoint

/-! # Zero neighbourhood of a section killed by the inverse-image unit

Source: Stacks Project, Tags 09XM and 03Q1.
(blueprint: lem-weil-pbc-etale-unit-zero-neighbourhood)
-/

@[expose] public section

universe u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry TopologicalSpace

-- The comap-stalk comparison across chosen pullbacks needs extra elaboration heartbeats.
set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
private theorem etaleUnit_zero_pointed_witness
    {X T : Scheme.{u + 1}} (p : T ⟶ X)
    (H : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1} ⥤
      Sheaf T.smallEtaleTopology AddCommGrpCat.{u + 1})
    (hH : H ⊣ p.Etale.sheafPushforwardContinuous
      AddCommGrpCat.{u + 1} X.smallEtaleTopology T.smallEtaleTopology)
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1})
    (V : X.Etale) (s : F.obj.obj (op V))
    (hs : (hH.unit.app F).hom.app (op V) s = 0)
    (t : (pullback V.hom p : Scheme)) :
    ∃ (W : X.Etale) (g : W ⟶ V) (w : W.left),
      g.left w = pullback.fst V.hom p t ∧ F.obj.map g.op s = 0 := by
  classical
  let := hH.isRightAdjoint
  let P := pullback V.hom p
  let y₀ := P.algClosurePoint t
  let y := y₀ ≫ pullback.snd V.hom p
  let Φ := Scheme.pointSmallEtale y
  let Ψ := Φ.comap p.Etale (Scheme.Hom.coverPreserving_etale p)
  let v : Ψ.fiber.obj V := Over.homMk y₀
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
        Φ.toPresheafFiber (p.Etale.obj V) v (H.obj F).obj := by
    rw [← Category.assoc,
      GrothendieckTopology.Point.toPresheafFiber_sheafFiberComapIso_hom_app]
    rw [Category.assoc, GrothendieckTopology.Point.toPresheafFiber_naturality]
    rw [← Category.assoc, huV]
  have hz : Ψ.toPresheafFiber V v F.obj s = 0 := by
    apply (ConcreteCategory.bijective_of_isIso
      ((c.hom.app F) ≫ Φ.presheafFiber.map (e.hom.app F).hom)).1
    have he := congrArg (fun k ↦ k s) hg
    change (Φ.presheafFiber.map (e.hom.app F).hom)
      ((c.hom.app F) (Ψ.toPresheafFiber V v F.obj s)) =
      (Φ.presheafFiber.map (e.hom.app F).hom) ((c.hom.app F) 0)
    rw [map_zero, map_zero]
    simp only [AddCommGrpCat.comp_apply] at he
    erw [hs, map_zero] at he
    exact he
  have heq : Ψ.toPresheafFiber V v F.obj s =
      Ψ.toPresheafFiber V v F.obj 0 := by simpa only [map_zero] using hz
  obtain ⟨W, g, w, hw, hzero⟩ := (Ψ.toPresheafFiber_eq_iff' V v s 0).mp heq
  let z : W.left := pullback.fst W.hom p
    (w.left (default : Spec (.of (AlgebraicClosure (P.residueField t)))))
  refine ⟨W, g, z, ?_, ?_⟩
  · have hw' := congrArg (fun k ↦ k.left ≫ pullback.fst V.hom p) hw
    change w.left ≫ (p.Etale.map g).left ≫ pullback.fst V.hom p =
      y₀ ≫ pullback.fst V.hom p at hw'
    rw [Scheme.Hom.etale_map_left_comp_fst] at hw'
    have he := congrArg
      (fun k ↦ k (default : Spec (.of (AlgebraicClosure (P.residueField t))))) hw'
    change g.left (pullback.fst W.hom p
      (w.left (default : Spec (.of (AlgebraicClosure (P.residueField t)))))) =
      pullback.fst V.hom p t
    simp only [Scheme.Hom.comp_apply] at he
    change g.left (pullback.fst W.hom p
      (w.left (default : Spec (.of (AlgebraicClosure (P.residueField t)))))) =
      pullback.fst V.hom p (P.algClosurePoint t
        (default : Spec (.of (AlgebraicClosure (P.residueField t))))) at he
    have hpoint : P.algClosurePoint t
        (default : Spec (.of (AlgebraicClosure (P.residueField t)))) = t :=
      Scheme.algClosurePoint_base P t _
    exact he.trans (congrArg (fun x : P ↦ pullback.fst V.hom p x) hpoint)
  · simpa only [map_zero] using hzero

set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
/-- A section killed on the whole base-changed object vanishes near its image.
Source: Stacks Project, Tag 09XM (equality locus) and Tag 03Q1 (pullback stalks).
(blueprint: lem-weil-pbc-etale-unit-zero-neighbourhood).
Proof: At a point of V ×_X T choose a geometric point above it. The inverse-image
stalk comparison, compatible with the adjunction unit, identifies the germ of s
at its image in V with the germ of its unit image. The latter is zero by hs.
A zero geometric germ is represented by an étale neighbourhood on which s is zero.
Its image in V is open; the neighbourhood covers that image, so sheaf separatedness
makes s zero on the image. Take the union of all such opens. Sheaf separatedness
on their open covering makes s zero on this union, which contains the image of
V ×_X T. The uniqueness isomorphism of left adjoints identifies the supplied unit
with the standard inverse-image unit. For an empty base change the image is empty
and the empty open works; the zero section permits the whole open. -/
theorem etaleUnit_zero_neighbourhood
    {X T : Scheme.{u + 1}} (p : T ⟶ X)
    (H : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1} ⥤
      Sheaf T.smallEtaleTopology AddCommGrpCat.{u + 1})
    (hH : H ⊣ p.Etale.sheafPushforwardContinuous
      AddCommGrpCat.{u + 1} X.smallEtaleTopology T.smallEtaleTopology)
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1})
    (V : X.Etale) (s : F.obj.obj (op V))
    (hs : (hH.unit.app F).hom.app (op V) s = 0) :
    ∃ (U : V.left.Opens), Set.range (pullback.fst V.hom p) ⊆ (U : Set V.left) ∧
      F.obj.map (MorphismProperty.Over.homMk
        (A := Scheme.Etale.mk (U.ι ≫ V.hom)) (B := V) U.ι rfl).op s = 0 := by
  classical
  let P : Scheme := pullback V.hom p
  choose W g w hw hz using etaleUnit_zero_pointed_witness p H hH F V s hs
  let O : P → V.left.Opens := fun t ↦
    ⟨Set.range (g t).left, (g t).left.isOpenMap.isOpen_range⟩
  let U : V.left.Opens := ⨆ t, O t
  let B : X.Etale := Scheme.Etale.mk (U.ι ≫ V.hom)
  let j : B ⟶ V := MorphismProperty.Over.homMk U.ι rfl
  have hU (t : P) : Set.range (g t).left ⊆ (U : Set V.left) :=
    show O t ≤ U from le_iSup O t
  let q (t : P) : (W t).left ⟶ U.toScheme :=
    IsOpenImmersion.lift U.ι (g t).left (by rw [Scheme.Opens.range_ι]; exact hU t)
  have hq (t : P) : q t ≫ U.ι = (g t).left :=
    IsOpenImmersion.lift_fac _ _ _
  let q' (t : P) : W t ⟶ B :=
    MorphismProperty.Over.homMk (q t) (by
      change q t ≫ U.ι ≫ V.hom = (W t).hom
      rw [← Category.assoc, hq, MorphismProperty.Over.w])
  have hfac (t : P) : q' t ≫ j = g t := by
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


