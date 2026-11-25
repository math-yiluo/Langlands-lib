/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.LocalOverlapTransitions
public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
public import Mathlib.RingTheory.Noetherian.Basic
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.ChosenPullback
public import Mathlib.AlgebraicGeometry.Pullbacks
import WeilConjectures.AlgebraicGeometry.FinitePresentationChartMapZeroEventually
import WeilConjectures.AlgebraicGeometry.Modules.FiniteDescent

/-! # Persistent eventual diagonal overlap equation

Source: Stacks Project, Tags 01ZR and 05N7.
(blueprint: lem-pc-fp-overlap-diagonal-eventually). -/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry

private lemma conjugate_eq_id {C : Type*} [Category C] {A B : C}
    (e : A ≅ B) (φ : B ⟶ B) : e.hom ≫ φ ≫ e.inv = 𝟙 _ ↔ φ = 𝟙 _ := by
  constructor
  · intro h
    have hh := congrArg (fun z ↦ e.inv ≫ z ≫ e.hom) h
    simpa using hh
  · rintro rfl
    simp

set_option backward.isDefEq.respectTransparency false in
private theorem diagonal_pull_iff
    {ι : Type u} {S S' : Scheme.{u}} {X X' : ι → Scheme.{u}}
    {f : ∀ a, X a ⟶ S} {f' : ∀ a, X' a ⟶ S'}
    {p : S' ⟶ S} {s : ∀ a, X' a ⟶ X a}
    (w : ∀ a, s a ≫ f a = f' a ≫ p)
    (T : modulesPseudofunctor.OverlapTransitions f) (a : ι) :
    (T.pull (α := fun a ↦ a) w).hom (f' a) (𝟙 _) (𝟙 _)
        (Category.id_comp _) (Category.id_comp _) = 𝟙 _ ↔
      (Scheme.Modules.pullback (s a)).map
        (T.hom (f a) (𝟙 _) (𝟙 _) (Category.id_comp _) (Category.id_comp _)) = 𝟙 _ := by
  have hn := T.pullHom_hom (s a) (f a) (f' a ≫ p) (w a)
    (𝟙 _) (𝟙 _) (Category.id_comp _) (Category.id_comp _)
    (s a) (s a) (Category.comp_id _) (Category.comp_id _)
  change CategoryTheory.Pseudofunctor.OverlapTransitions.pulledHom w T
    (f' a) (𝟙 _) (𝟙 _)
    (Category.id_comp _) (Category.id_comp _) = 𝟙 _ ↔ _
  rw [CategoryTheory.Pseudofunctor.OverlapTransitions.pulledHom_eq w T
    (f' a) (𝟙 _) (𝟙 _)
    (f' a ≫ p) (s a) (s a) (Category.id_comp _) (Category.id_comp _)
    rfl (Category.id_comp _) (Category.id_comp _)]
  rw [← hn]
  dsimp only [CategoryTheory.Pseudofunctor.LocallyDiscreteOpToCat.pullHom]
  let e := (Cat.Hom.toNatIso (modulesPseudofunctor.mapComp'
    (s a).op.toLoc (𝟙 (X' a)).op.toLoc (s a).op.toLoc (by simp))).app (T.obj a)
  let d := (Cat.Hom.toNatIso (modulesPseudofunctor.mapComp'
    (𝟙 (X a)).op.toLoc (s a).op.toLoc (s a).op.toLoc (by simp))).app (T.obj a)
  change e.inv ≫ (d.hom ≫ _ ≫ d.inv) ≫ e.hom = 𝟙 _ ↔ _
  exact (conjugate_eq_id e.symm _).trans (conjugate_eq_id d _)

private lemma pullback_map_zero_of_comp
    {X Y Z : Scheme.{u}} (g : Z ⟶ Y) (f : Y ⟶ X) (h : Z ⟶ X)
    (hw : g ≫ f = h) {M N : X.Modules} (δ : M ⟶ N)
    (hz : (Scheme.Modules.pullback f).map δ = 0) :
    (Scheme.Modules.pullback h).map δ = 0 := by
  subst h
  have hn := (Scheme.Modules.pullbackComp g f).hom.naturality δ
  dsimp at hn
  rw [hz, Functor.map_zero, zero_comp] at hn
  apply (cancel_epi ((Scheme.Modules.pullbackComp g f).hom.app M)).mp
  simpa using hn.symm

private lemma refinement_comp
    {S X Y Z : Scheme.{u}} (U : S.OpenCover.{u})
    (qX : X ⟶ S) (qY : Y ⟶ S) (qZ : Z ⟶ S)
    (rYX : Y ⟶ X) (rZY : Z ⟶ Y) (rZX : Z ⟶ X)
    (hYX : rYX ≫ qX = qY) (hZY : rZY ≫ qY = qZ) (hZX : rZX ≫ qX = qZ)
    (hcomp : rZY ≫ rYX = rZX) (a : U.I₀) :
    overlapRefinementHom U qY qZ rZY hZY a ≫
      overlapRefinementHom U qX qY rYX hYX a =
    overlapRefinementHom U qX qZ rZX hZX a := by
  apply pullback.hom_ext
  · change (overlapRefinementHom U qY qZ rZY hZY a ≫
      overlapRefinementHom U qX qY rYX hYX a) ≫ (U.pullback₁ qX).f a =
      overlapRefinementHom U qX qZ rZX hZX a ≫ (U.pullback₁ qX).f a
    rw [Category.assoc, overlapRefinementHom_map, ← Category.assoc,
      overlapRefinementHom_map, Category.assoc, hcomp, overlapRefinementHom_map]
  · change (overlapRefinementHom U qY qZ rZY hZY a ≫
      overlapRefinementHom U qX qY rYX hYX a) ≫ U.pullbackHom qX a =
      overlapRefinementHom U qX qZ rZX hZX a ≫ U.pullbackHom qX a
    rw [Category.assoc, overlapRefinementHom_comp, overlapRefinementHom_comp,
      overlapRefinementHom_comp]

-- The existing existential witness `hkl` is not used in the statement after its binder.
set_option linter.unusedVariables false in
/-- The identity defect of a single cover chart vanishes eventually, and remains
zero at every later stage.
Source: Stacks Project, Tag 01ZR (3), finite-type zero-map descent.
(blueprint: lem-pc-fp-overlap-diagonal-eventually).

Proof: On the chart at k subtract the identity from its self transition. Its source
and target are pullbacks of the prescribed finitely presented quasi-coherent module,
up to the supplied component isomorphism. The source is therefore of finite type.
The chart is quasi-compact over Spec(R_k), as an affine chart base changed along
an affine map. The identity-base-change comparison identifies this defect with a
map to which finitePresentation_zero_map_descent applies. Naturality of transitions,
the pullback composition comparisons, and limit coherence show that its limit
pullback is zero. Zero-map descent gives l. At any m above l the defect is still
zero since pullback is additive. The canonical chart refinement maps compose,
by the pullback universal property, and pseudofunctor associativity identifies
this pullback defect with the self transition of the prescribed T' minus identity.
Thus the displayed equation holds. This also handles zero modules and empty charts;
the theorem is only invoked for an actual cover index. -/
theorem finitePresentation_overlap_diagonal_eventually
    {I : Type u} [Preorder I] [IsDirected I (· ≤ ·)]
    (R : I ⥤ CommRingCat.{u})
    (c : Cone (R.op ⋙ Scheme.Spec)) (hc : IsLimit c) [IsAffine c.pt]
    (i : I) {Xi : Scheme.{u}} (f : Xi ⟶ Spec (R.obj i))
    [LocallyOfFinitePresentation f] [QuasiCompact f] [QuasiSeparated f]
    (j : I) (hij : i ≤ j)
    (U : (pullback f (Spec.map (R.map (homOfLE hij)))).OpenCover.{u})
    [Finite U.I₀] [∀ a, IsAffine (U.X a)]
    (N : (a : U.I₀) → (U.X a).Modules)
    (a : U.I₀)
    (hN : ∀ a, (N a).IsFinitePresentation) (hNq : ∀ a, (N a).IsQuasicoherent)
    :
    ∀ (k : I) (hjk : j ≤ k),
      let q₀ := overlapStageMap R f hij hjk
      let V₀ : (pullback f (Spec.map (R.map (homOfLE (hij.trans hjk))))).OpenCover.{u} :=
        U.pullback₁ q₀
      let p₀ := overlapLimitMap R c f (hij.trans hjk)
      ∀ T : modulesPseudofunctor.OverlapTransitions V₀.f,
        (∀ a, Nonempty ((T.obj a : (V₀.X a).Modules) ≅
          (Scheme.Modules.pullback (U.pullbackHom q₀ a)).obj (N a))) →
        (T.pull (p := p₀) (α := fun a ↦ a)
          (fun a ↦ V₀.pullbackHom_map p₀ a)).Coherent →
        ∃ (l : I) (hkl : k ≤ l), ∀ (m : I) (hkm : k ≤ m), l ≤ m →
          let q := overlapStageMap R f hij (hjk.trans hkm)
          let V : (pullback f (Spec.map
              (R.map (homOfLE (hij.trans (hjk.trans hkm)))))).OpenCover.{u} :=
            U.pullback₁ q
          let r := overlapStageMap R f (hij.trans hjk) hkm
          let s := overlapRefinementHom U q₀ q r
            (overlapStageMap_comp R f hij hjk hkm)
          let T' := T.pull (p := r) (α := fun a ↦ a) (p' := s)
            (fun a ↦ overlapRefinementHom_map U q₀ q r
              (overlapStageMap_comp R f hij hjk hkm) a)
          T'.hom (V.f a) (𝟙 _) (𝟙 _) (Category.id_comp _) (Category.id_comp _) = 𝟙 _ := by
  intro k hjk q₀ V₀ p₀ T he hT
  obtain ⟨e⟩ := he a
  let := hN a
  have : (T.obj a : (V₀.X a).Modules).IsFinitePresentation :=
    Scheme.Modules.isFinitePresentation_of_iso e.symm
  let M := (Scheme.Modules.pullback (𝟙 (V₀.X a))).obj (T.obj a)
  have : M.IsFinitePresentation := inferInstance
  let d : M ⟶ M :=
    T.hom (V₀.f a) (𝟙 _) (𝟙 _) (Category.id_comp _) (Category.id_comp _)
  have hlim : (Scheme.Modules.pullback (V₀.pullbackHom p₀ a)).map d = 𝟙 _ :=
    (diagonal_pull_iff (fun b ↦ V₀.pullbackHom_map p₀ b) T a).mp
      (hT.hom_self _ (𝟙 _) (Category.id_comp _))
  have hz : (Scheme.Modules.pullback (V₀.pullbackHom p₀ a)).map (d - 𝟙 M) = 0 := by
    rw [Functor.map_sub, CategoryTheory.Functor.map_id, hlim, sub_self]
  obtain ⟨l, hkl, hl⟩ := finitePresentation_chart_map_zero_eventually
    R c hc i f j hij U a k hjk M M inferInstance inferInstance
    inferInstance inferInstance (d - 𝟙 M) hz
  refine ⟨l, hkl, ?_⟩
  intro m hkm hlm q V r s T'
  apply (diagonal_pull_iff
    (fun b ↦ overlapRefinementHom_map U q₀ q r
      (overlapStageMap_comp R f hij hjk hkm) b) T a).mpr
  let ql := overlapStageMap R f hij (hjk.trans hkl)
  let rkl := overlapStageMap R f (hij.trans hjk) hkl
  let rlm := overlapStageMap R f (hij.trans (hjk.trans hkl)) hlm
  let skl := overlapRefinementHom U q₀ ql rkl
    (overlapStageMap_comp R f hij hjk hkl) a
  let slm := overlapRefinementHom U ql q rlm
    (overlapStageMap_comp R f hij (hjk.trans hkl) hlm) a
  have hs : slm ≫ skl = s a :=
    refinement_comp U q₀ ql q rkl rlm r
      (overlapStageMap_comp R f hij hjk hkl)
      (overlapStageMap_comp R f hij (hjk.trans hkl) hlm)
      (overlapStageMap_comp R f hij hjk hkm)
      (overlapStageMap_comp R f (hij.trans hjk) hkl hlm) a
  have hm := pullback_map_zero_of_comp slm skl (s a) hs (d - 𝟙 M) hl
  rw [Functor.map_sub, CategoryTheory.Functor.map_id, sub_eq_zero] at hm
  exact hm

end AlgebraicGeometry
