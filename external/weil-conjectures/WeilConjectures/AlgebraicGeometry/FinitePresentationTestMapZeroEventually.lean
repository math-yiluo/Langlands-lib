/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.LocalOverlapTransitions
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Quasicoherent
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact
import WeilConjectures.AlgebraicGeometry.FinitePresentationZeroMapDescent
import WeilConjectures.AlgebraicGeometry.Modules.FiniteDescent

/-! # Eventual vanishing on a quasi-compact test scheme

Source: Stacks Project, Tag 01ZR (3), affine vanishing and Zariski gluing.
(blueprint: lem-pc-fp-test-map-zero-eventually). -/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry

private lemma map_zero_iff_of_natIso
    {C D : Type*} [Category C] [Category D] [Preadditive D]
    {P Q : C ⥤ D} (e : P ≅ Q) {M N : C} (δ : M ⟶ N) :
    P.map δ = 0 ↔ Q.map δ = 0 := by
  constructor
  · intro hz
    have hn := e.hom.naturality δ
    rw [hz, zero_comp] at hn
    apply (cancel_epi (e.hom.app M)).mp
    simpa using hn.symm
  · intro hz
    have hn := e.hom.naturality δ
    rw [hz, comp_zero] at hn
    apply (cancel_mono (e.hom.app N)).mp
    simpa using hn

private lemma tensor_zero_iff {X Y : Scheme.{u}} (g : X ⟶ Y)
    {M N : Y.Modules} (δ : M ⟶ N) :
    (Scheme.Modules.tensorPullback g).map δ = 0 ↔
      (Scheme.Modules.pullback g).map δ = 0 := by
  obtain ⟨adj⟩ := Scheme.Modules.nonempty_tensorPullbackAdjunction g
  exact map_zero_iff_of_natIso
    (adj.leftAdjointUniq (Scheme.Modules.pullbackPushforwardAdjunction g)) δ

private lemma pullback_zero_comp_iff {X Y Z : Scheme.{u}} (g : Z ⟶ Y) (f : Y ⟶ X)
    {M N : X.Modules} (δ : M ⟶ N) :
    (Scheme.Modules.pullback (g ≫ f)).map δ = 0 ↔
      (Scheme.Modules.pullback g).map ((Scheme.Modules.pullback f).map δ) = 0 :=
  (map_zero_iff_of_natIso (Scheme.Modules.pullbackComp g f) δ).symm

private lemma pullback_zero_of_comp {X Y Z : Scheme.{u}}
    (g : Z ⟶ Y) (f : Y ⟶ X) (h : Z ⟶ X) (hw : g ≫ f = h)
    {M N : X.Modules} (δ : M ⟶ N)
    (hz : (Scheme.Modules.pullback f).map δ = 0) :
    (Scheme.Modules.pullback h).map δ = 0 := by
  subst h
  apply (pullback_zero_comp_iff g f δ).mpr
  rw [hz, Functor.map_zero]

set_option backward.isDefEq.respectTransparency false in
/-- A module map on a quasi-compact test scheme over a stage vanishes at a later stage
if its pullback to the limit is zero. Both modules are finitely presented and quasi-coherent.
Source: Stacks Project, Tag 01ZR (3), affine vanishing and Zariski gluing.
(blueprint: lem-pc-fp-test-map-zero-eventually).

Proof: Put b = t followed by the structural map to Spec(R_k). Apply
finitePresentation_zero_map_descent to b, with both initial indices equal to k.
Transport F, G and δ along the canonical isomorphism from the pullback of b along
identity to W. Its limit base change is canonically isomorphic to the pullback
of t along overlapLimitMap: both objects represent pairs of a point of W and a
point of the limit lying over the same point of Spec(R_k). At a later index l,
the same pullback-pasting argument identifies the base change with the pullback
of t along overlapStageMap. These isomorphisms commute with the projections to W
by uniqueness in the pullback universal property. The module pullback comparison
is obtained from pullbackComp and the natural isomorphism between moduleBaseChange
and the native pullback: both are left adjoint to the same pushforward. Naturality
of these isomorphisms and cancellation of their invertible components transport
zero in both directions. The zero-map descent theorem now gives l. Its hypotheses
hold because b is quasi-compact, F is finitely presented (hence finite type) and
quasi-coherent, and G is
finitely presented and quasi-coherent. Empty W, zero modules, identity transition
maps and a singleton index set require no exceptions. -/
theorem finitePresentation_test_map_zero_eventually
    {I : Type u} [Preorder I] [IsDirected I (· ≤ ·)]
    (R : I ⥤ CommRingCat.{u})
    (c : Cone (R.op ⋙ Scheme.Spec)) (hc : IsLimit c) [IsAffine c.pt]
    (i : I) {Xi : Scheme.{u}} (f : Xi ⟶ Spec (R.obj i))
    (k : I) (hik : i ≤ k) {W : Scheme.{u}}
    (t : W ⟶ pullback f (Spec.map (R.map (homOfLE hik))))
    [QuasiCompact (t ≫ pullback.snd f (Spec.map (R.map (homOfLE hik))))]
    (F G : W.Modules)
    (hF_fp : F.IsFinitePresentation) (hF_qc : F.IsQuasicoherent)
    (hG_fp : G.IsFinitePresentation) (hG_qc : G.IsQuasicoherent)
    (δ : F ⟶ G)
    (hδ : (Scheme.Modules.pullback
      (pullback.fst t (overlapLimitMap R c f hik))).map δ = 0) :
    ∃ (l : I) (hkl : k ≤ l),
      (Scheme.Modules.pullback
        (pullback.fst t (overlapStageMap R f hik hkl))).map δ = 0 := by
  classical
  let b := t ≫ pullback.snd f (Spec.map (R.map (homOfLE hik)))
  let v₀ := Spec.map (R.map (homOfLE (le_refl k)))
  let π₀ := pullback.fst b v₀
  let F₀ := (Scheme.Modules.pullback π₀).obj F
  let G₀ := (Scheme.Modules.pullback π₀).obj G
  let δ₀ := (Scheme.Modules.pullback π₀).map δ
  let := hF_fp
  let := hF_qc
  let := hG_fp
  let := hG_qc
  have : F₀.IsFinitePresentation := inferInstance
  have : F₀.IsQuasicoherent := inferInstance
  have : G₀.IsFinitePresentation := inferInstance
  have : G₀.IsQuasicoherent := inferInstance
  let aLimit : Over.mk (c.π.app (op k)) ⟶ Over.mk v₀ :=
    Over.homMk (c.π.app (op k)) (by dsimp [v₀]; simp)
  let gLimit : Over.mk (c.π.app (op i)) ⟶
      Over.mk (Spec.map (R.map (homOfLE hik))) :=
    Over.homMk (c.π.app (op k)) (c.w (homOfLE hik).op)
  have hpLimit := (IsPullback.of_hasPullback t (overlapLimitMap R c f hik)).paste_vert
    (isPullback_baseChangeMap f gLimit)
  let eLimit := hpLimit.isoPullback
  have hzLimit : (Scheme.Modules.pullback (pullback.fst b (c.π.app (op k)))).map δ = 0 :=
    pullback_zero_of_comp eLimit.inv (pullback.fst t (overlapLimitMap R c f hik))
      (pullback.fst b (c.π.app (op k))) (by
        rw [← hpLimit.isoPullback_hom_fst, ← Category.assoc,
          Iso.inv_hom_id, Category.id_comp]
        rfl) δ hδ
  have hz₀ : (Scheme.Modules.moduleBaseChange b aLimit).map δ₀ = 0 := by
    apply (tensor_zero_iff (baseChangeMap b aLimit) δ₀).mpr
    apply (pullback_zero_comp_iff (baseChangeMap b aLimit) π₀ δ).mp
    change (Scheme.Modules.pullback
      (baseChangeMap b aLimit ≫ pullback.fst b v₀)).map δ = 0
    have hp : baseChangeMap b aLimit ≫ pullback.fst b v₀ =
        pullback.fst b (c.π.app (op k)) := baseChangeMap_fst b aLimit
    rw [hp]
    exact hzLimit
  obtain ⟨l, hkl, hl⟩ := finitePresentation_zero_map_descent
    R c hc k b k (le_refl k) F₀ G₀ inferInstance inferInstance
    inferInstance inferInstance δ₀ hz₀
  refine ⟨l, hkl, ?_⟩
  let aStage : Over.mk (Spec.map (R.map (homOfLE hkl))) ⟶ Over.mk v₀ :=
    Over.homMk (Spec.map (R.map (homOfLE hkl))) (by dsimp [v₀]; simp)
  have hzStage : (Scheme.Modules.pullback
      (pullback.fst b (Spec.map (R.map (homOfLE hkl))))).map δ = 0 := by
    have hn := (tensor_zero_iff (baseChangeMap b aStage) δ₀).mp hl
    have hm := (pullback_zero_comp_iff (baseChangeMap b aStage) π₀ δ).mpr hn
    change (Scheme.Modules.pullback
      (baseChangeMap b aStage ≫ pullback.fst b v₀)).map δ = 0 at hm
    have hp : baseChangeMap b aStage ≫ pullback.fst b v₀ =
        pullback.fst b (Spec.map (R.map (homOfLE hkl))) := baseChangeMap_fst b aStage
    rw [hp] at hm
    exact hm
  let gStage : Over.mk (Spec.map (R.map (homOfLE (hik.trans hkl)))) ⟶
      Over.mk (Spec.map (R.map (homOfLE hik))) :=
    Over.homMk (Spec.map (R.map (homOfLE hkl)))
      (by dsimp; rw [← Spec.map_comp, ← R.map_comp]; rfl)
  have hpStage := (IsPullback.of_hasPullback t (overlapStageMap R f hik hkl)).paste_vert
    (isPullback_baseChangeMap f gStage)
  exact pullback_zero_of_comp hpStage.isoPullback.hom
    (pullback.fst b (Spec.map (R.map (homOfLE hkl))))
    (pullback.fst t (overlapStageMap R f hik hkl)) hpStage.isoPullback_hom_fst δ hzStage

end AlgebraicGeometry
