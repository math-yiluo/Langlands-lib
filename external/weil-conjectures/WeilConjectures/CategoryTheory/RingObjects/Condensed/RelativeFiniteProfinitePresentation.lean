/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.Topology.Category.Profinite.AsLimit
public import Mathlib.Topology.Category.Profinite.Limits
public import Mathlib.CategoryTheory.Limits.Constructions.Over.Basic

/-!
# Relative finite presentations of profinite spaces

Source: Bhatt--Scholze, proof of Lemma 2.2.8, relative finite clopen partitions.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits Topology Opposite

namespace Profinite

private structure RelativePartition {S : Profinite.{u}} (E : Over S) where
  source : DiscreteQuotient E.left
  base : DiscreteQuotient S
  compatible : DiscreteQuotient.LEComap E.hom.hom.hom source base

private instance {S : Profinite.{u}} (E : Over S) : Preorder (RelativePartition E) where
  le i j := i.source ≤ j.source ∧ i.base ≤ j.base
  le_refl _ := ⟨le_rfl, le_rfl⟩
  le_trans _ _ _ h k := ⟨h.1.trans k.1, h.2.trans k.2⟩

set_option backward.isDefEq.respectTransparency false in
private def coarsePartition {S : Profinite.{u}} (E : Over S)
    (Q : DiscreteQuotient E.left) : RelativePartition E :=
  ⟨Q, ⊤, le_top⟩

private instance {S : Profinite.{u}} (E : Over S) : Nonempty (RelativePartition E) :=
  ⟨coarsePartition E ⊤⟩

private instance {S : Profinite.{u}} (E : Over S) :
    IsDirected (RelativePartition E) (· ≥ ·) where
  directed i j := by
    refine ⟨⟨i.source ⊓ j.source, i.base ⊓ j.base, ?_⟩,
      ⟨inf_le_left, inf_le_left⟩, ⟨inf_le_right, inf_le_right⟩⟩
    exact le_inf (inf_le_left.trans i.compatible) (inf_le_right.trans j.compatible)

set_option backward.isDefEq.respectTransparency false in
private def partitionQuotient {S : Profinite.{u}} (E : Over S)
    (i : RelativePartition E) : S ⟶ FintypeCat.toProfinite.obj (FintypeCat.of i.base) :=
  (S.asLimitCone.π.app i.base)

set_option backward.isDefEq.respectTransparency false in
private def partitionMap {S : Profinite.{u}} (E : Over S)
    (i : RelativePartition E) : FintypeCat.of i.source ⟶ FintypeCat.of i.base :=
  FintypeCat.homMk (DiscreteQuotient.map E.hom.hom.hom i.compatible)

private abbrev partitionStage {S : Profinite.{u}} (E : Over S)
    (i : RelativePartition E) : Over S :=
  Over.mk (CompHausLike.pullback.fst (partitionQuotient E i)
    (FintypeCat.toProfinite.map (partitionMap E i)))

set_option backward.isDefEq.respectTransparency false in
private def partitionTransition {S : Profinite.{u}} (E : Over S)
    {i j : RelativePartition E} (h : i ≤ j) : partitionStage E i ⟶ partitionStage E j :=
  Over.homMk (CompHausLike.pullback.lift (partitionQuotient E j)
    (FintypeCat.toProfinite.map (partitionMap E j))
    (CompHausLike.pullback.fst (partitionQuotient E i)
      (FintypeCat.toProfinite.map (partitionMap E i)))
    (CompHausLike.pullback.snd (partitionQuotient E i)
        (FintypeCat.toProfinite.map (partitionMap E i)) ≫
      FintypeCat.toProfinite.map (FintypeCat.homMk (DiscreteQuotient.ofLE h.1))) (by
        ext x
        change j.base.proj x.1.1 =
          DiscreteQuotient.map E.hom.hom.hom j.compatible
            (DiscreteQuotient.ofLE h.1 x.1.2)
        rw [DiscreteQuotient.map_ofLE]
        have hx : i.base.proj x.1.1 =
            DiscreteQuotient.map E.hom.hom.hom i.compatible x.1.2 := x.2
        simpa only [DiscreteQuotient.ofLE_proj, DiscreteQuotient.ofLE_map] using
          congrArg (DiscreteQuotient.ofLE h.2) hx)) (by rfl)

set_option backward.isDefEq.respectTransparency false in
private def partitionDiagram {S : Profinite.{u}} (E : Over S) :
    RelativePartition E ⥤ Over S where
  obj := partitionStage E
  map h := partitionTransition E h.le
  map_id _ := by
    ext x
    apply Subtype.ext
    exact Prod.ext rfl (DiscreteQuotient.ofLE_refl_apply _)
  map_comp f g := by
    ext x
    apply Subtype.ext
    exact Prod.ext rfl (congrFun (DiscreteQuotient.ofLE_comp_ofLE f.le.1 g.le.1) x.1.2).symm

set_option backward.isDefEq.respectTransparency false in
private def partitionCone {S : Profinite.{u}} (E : Over S) :
    Cone (partitionDiagram E) where
  pt := E
  π :=
    { app := fun i ↦ Over.homMk
        (CompHausLike.pullback.lift (partitionQuotient E i)
          (FintypeCat.toProfinite.map (partitionMap E i)) E.hom
          (E.left.asLimitCone.π.app i.source) (by ext x; rfl)) (by rfl)
      naturality := fun i j h ↦ by
        ext x
        apply Subtype.ext
        exact Prod.ext rfl (DiscreteQuotient.ofLE_proj h.le.1 x).symm }

set_option backward.isDefEq.respectTransparency false in
private noncomputable def partitionConeIsLimit {S : Profinite.{u}} (E : Over S) :
    IsLimit (partitionCone E) := by
  classical
  let d (c : Cone (partitionDiagram E)) : Cone E.left.diagram :=
    { pt := c.pt.left
      π :=
        { app := fun Q ↦ (c.π.app (coarsePartition E Q)).left ≫
            CompHausLike.pullback.snd _ _
          naturality := fun Q R h ↦ by
            have he := congrArg (fun k ↦ k.left) (c.w
              (show coarsePartition E Q ⟶ coarsePartition E R from homOfLE ⟨h.le, le_rfl⟩))
            ext x
            exact (congrArg (fun k ↦ (k x).1.2) he).symm } }
  let e (c : Cone (partitionDiagram E)) := E.left.asLimit.lift (d c)
  have he (c : Cone (partitionDiagram E)) (Q : DiscreteQuotient E.left) (x : c.pt.left) :
      Q.proj (e c x) = ((c.π.app (coarsePartition E Q)).left x).1.2 :=
    ConcreteCategory.congr_hom (E.left.asLimit.fac (d c) Q) x
  have hw (c : Cone (partitionDiagram E)) : e c ≫ E.hom = c.pt.hom := by
    ext x
    apply DiscreteQuotient.eq_of_forall_proj_eq
    intro Q
    let i : RelativePartition E := ⟨Q.comap E.hom.hom.hom, Q, le_rfl⟩
    have hi : ((c.π.app i).left x).1.2 =
        ((c.π.app (coarsePartition E i.source)).left x).1.2 := by
      have h := congrArg (fun k ↦ ((k.left x).1.2))
        (c.w (show i ⟶ coarsePartition E i.source from homOfLE ⟨le_rfl, le_top⟩))
      change DiscreteQuotient.ofLE (le_refl i.source) ((c.π.app i).left x).1.2 = _ at h
      rw [DiscreteQuotient.ofLE_refl_apply] at h
      exact h
    have hiw := ConcreteCategory.congr_hom (c.π.app i).w x
    change Q.proj (E.hom (e c x)) = Q.proj (c.pt.hom x)
    erw [← DiscreteQuotient.map_proj i.compatible, he, ← hi]
    exact (((c.π.app i).left x).2.symm).trans (congrArg Q.proj hiw)
  refine { lift := fun c ↦ Over.homMk (e c) (hw c), fac := ?_, uniq := ?_ }
  · intro c i
    apply Over.OverMorphism.ext
    ext x
    apply Subtype.ext
    apply Prod.ext
    · exact (ConcreteCategory.congr_hom (hw c) x).trans
        (ConcreteCategory.congr_hom (c.π.app i).w x).symm
    · have hi : ((c.π.app i).left x).1.2 =
          ((c.π.app (coarsePartition E i.source)).left x).1.2 :=
        by
          have h := congrArg (fun k ↦ (k.left x).1.2)
            (c.w (show i ⟶ coarsePartition E i.source from homOfLE ⟨le_rfl, le_top⟩))
          change DiscreteQuotient.ofLE (le_refl i.source) ((c.π.app i).left x).1.2 = _ at h
          rw [DiscreteQuotient.ofLE_refl_apply] at h
          exact h
      exact (he c i.source x).trans hi.symm
  · intro c m hm
    apply Over.OverMorphism.ext
    apply E.left.asLimit.hom_ext
    intro Q
    ext x
    change Q.proj (m.left x) = Q.proj (e c x)
    rw [he]
    exact congrArg (fun k ↦ (k.left x).1.2) (hm (coarsePartition E Q))

/-- Every profinite space over a profinite base has a small cofiltered presentation by
pullbacks of maps of finite sets along surjective finite quotients of the base.

Source: Bhatt--Scholze, proof of Lemma 2.2.8
(blueprint: new-lem-zl-relative-finite-profinite-presentation).

Proof: index by compatible finite clopen partitions of source and base. Common
intersection refines two such pairs, and trivial partitions give an object. A stage
is the base times the finite source quotient over the finite base quotient. The
canonical cone is limiting: its source coordinates for trivial base partition give
the original source by its finite-quotient limit. The other base partitions force
that point to lie over the specified base point. Refinement determines all stage
coordinates, proving uniqueness. The argument includes empty source and base. -/
theorem exists_relative_finite_presentation {S : Profinite.{u}} (E : Over S) :
    ∃ (I : Type u) (_ : SmallCategory I) (_ : IsCofiltered I)
      (D : I ⥤ Over S) (c : Cone D),
      c.pt = E ∧ Nonempty (IsLimit c) ∧ ∀ i : I,
        ∃ (A C : FintypeCat.{u}) (q : S ⟶ FintypeCat.toProfinite.obj C) (f : A ⟶ C),
          Function.Surjective q ∧
          Nonempty (D.obj i ≅ Over.mk (pullback.fst q (FintypeCat.toProfinite.map f))) := by
  classical
  refine ⟨RelativePartition E, inferInstance, inferInstance, partitionDiagram E,
    partitionCone E, rfl, ⟨partitionConeIsLimit E⟩, ?_⟩
  intro i
  refine ⟨FintypeCat.of i.source, FintypeCat.of i.base, partitionQuotient E i,
    partitionMap E i, DiscreteQuotient.proj_surjective i.base, ?_⟩
  let e := (CompHausLike.pullback.isLimit (partitionQuotient E i)
      (FintypeCat.toProfinite.map (partitionMap E i))).conePointUniqueUpToIso
    (pullback.isLimit _ _)
  refine ⟨Over.isoMk e ?_⟩
  exact (CompHausLike.pullback.isLimit _ _).conePointUniqueUpToIso_hom_comp
    (pullback.isLimit _ _) WalkingCospan.left

end Profinite
