/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.TensorPullbackCompositionIso
public import WeilConjectures.AlgebraicGeometry.OpenCoverTensorPullbackComparison
public import WeilConjectures.AlgebraicGeometry.ChartOrdinaryMapRecovery
import WeilConjectures.AlgebraicGeometry.ChartTensorPullbackComparisonCoherence

/-! # Transporting an ordinary chart lift to tensor pullback coordinates

Source: Stacks Project, Tags 0095 and 0096, functoriality of pullback.
(blueprint: lem-pc-chart-tensor-pullback-lift-transport).
-/

@[expose] public section
universe u
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

private theorem comparison_transport
    {C₀ C₁ C₂ C₃ C₄ C₅ C₆ : Type (u + 1)}
    [Category.{u} C₀] [Category.{u} C₁] [Category.{u} C₂] [Category.{u} C₃]
    [Category.{u} C₄] [Category.{u} C₅] [Category.{u} C₆]
    (A : C₀ ⥤ C₁) (B : C₁ ⥤ C₂) (B₀ : C₁ ⥤ C₃)
    (Q : C₂ ⥤ C₆) (R : C₃ ⥤ C₆)
    (Tq : C₀ ⥤ C₄) (Tp : C₄ ⥤ C₅) (T₀ : C₀ ⥤ C₅)
    (L : C₄ ⥤ C₂) (W : C₅ ⥤ C₃) (P : C₅ ⥤ C₆)
    (tq : A ⋙ B ≅ Tq ⋙ L) (tp : L ⋙ Q ≅ Tp ⋙ P)
    (t₀ : A ⋙ B₀ ≅ T₀ ⋙ W) (e : T₀ ≅ Tq ⋙ Tp)
    (d : B₀ ⋙ R ≅ B ⋙ Q) (b : W ⋙ R ≅ P)
    (F G : C₀) (φ : T₀.obj F ⟶ T₀.obj G) (s : B.obj (A.obj F) ⟶ B.obj (A.obj G))
    (hc : ∀ H, Q.map (tq.hom.app H) ≫ tp.hom.app (Tq.obj H) =
      d.inv.app (A.obj H) ≫ R.map (t₀.hom.app H) ≫
        b.hom.app (T₀.obj H) ≫ P.map (e.hom.app H))
    (hs : d.inv.app (A.obj F) ≫ R.map (t₀.hom.app F ≫ W.map φ ≫ t₀.inv.app G) ≫
      d.hom.app (A.obj G) = Q.map s) :
    tp.inv.app (Tq.obj F) ≫ Q.map (tq.inv.app F ≫ s ≫ tq.hom.app G) ≫
      tp.hom.app (Tq.obj G) = P.map (e.inv.app F ≫ φ ≫ e.hom.app G) := by
  let c (H : C₀) := Q.mapIso (tq.app H) ≪≫ tp.app (Tq.obj H)
  have hc' (H : C₀) : (c H).hom = d.inv.app (A.obj H) ≫
      R.map (t₀.hom.app H) ≫ b.hom.app (T₀.obj H) ≫ P.map (e.hom.app H) := hc H
  have hb := b.hom.naturality φ
  dsimp only [Functor.comp_map] at hb
  suffices h : (c F).inv ≫ Q.map s ≫ (c G).hom =
      P.map (e.inv.app F ≫ φ ≫ e.hom.app G) by
    simpa only [c, Iso.trans_inv, Iso.trans_hom, Functor.mapIso_inv, Functor.mapIso_hom,
      Iso.app_hom, Iso.app_inv, Functor.map_comp, Category.assoc] using h
  rw [← cancel_epi (c F).hom]
  simp only [Iso.hom_inv_id_assoc]
  rw [← hs]
  conv_rhs => lhs; rw [hc' F]
  conv_lhs => rhs; rw [hc' G]
  simp only [Functor.map_comp, Category.assoc, Iso.hom_inv_id_app_assoc]
  simp only [← Functor.map_comp_assoc, Iso.inv_hom_id_app, Iso.hom_inv_id_app_assoc]
  simp only [Functor.map_comp, Category.assoc]
  have hR := R.map_id ((T₀ ⋙ W).obj G)
  simp only [hR]
  have hI : (𝟙 (R.obj ((T₀ ⋙ W).obj G))) ≫
      b.hom.app (T₀.obj G) ≫ P.map (e.hom.app G) =
      b.hom.app (T₀.obj G) ≫ P.map (e.hom.app G) := Category.id_comp _
  simp only [hI]
  simpa only [Category.assoc] using congrArg
    (fun f ↦ d.inv.app (A.obj F) ≫ R.map (t₀.hom.app F) ≫ f ≫
      P.map (e.hom.app G)) hb


/-- A compatible ordinary chart map gives the canonical tensor chart equation.
Source: Stacks Project, Tags 0095 and 0096, composition and base change of pullback.
(blueprint: lem-pc-chart-tensor-pullback-lift-transport).

Proof: The map v is the unique pullback lift identifying the iterated chart
with the direct chart. Its second projection gives the congruence in d. Replace
all tensor pullbacks by ordinary pullbacks using the unique comparison of left
adjoints to the same pushforward. Under this comparison, tensor composition is
ordinary pullback composition; openCoverTensorPullbackComparison is restriction
followed by that same comparison. The ordinary pullback associativity identity
for v, the two chart projections and the ambient triangle makes the two ways
of composing these comparisons agree. Naturality then moves the ordinary map s
through the stage comparison. Substitute the assumed d equation, cancel adjacent
inverse comparisons, and obtain the displayed equation. This is a coherence
identity only: no finiteness, affinity, directedness or limit is used. -/
theorem chart_tensor_pullback_lift_transport
    {X Y Z : Scheme.{u}} (q : Y ⟶ X) (p : Z ⟶ Y) (q₀ : Z ⟶ X)
    (w : p ≫ q = q₀) (U : X.OpenCover.{u}) (a : U.I₀)
    (F G : X.Modules)
    (φ : (Scheme.Modules.tensorPullback q₀).obj F ⟶
      (Scheme.Modules.tensorPullback q₀).obj G) :
      let Uk : Y.OpenCover.{u} := U.pullback₁ q
      let V : Z.OpenCover.{u} := Uk.pullback₁ p
      let W : Z.OpenCover.{u} := U.pullback₁ q₀
      let t₀ := Scheme.Modules.openCoverTensorPullbackComparison q₀ U a
      let ψ := t₀.hom.app F ≫ (Scheme.Modules.pullback (W.f a)).map φ ≫ t₀.inv.app G
      ∀ s : (Scheme.Modules.pullback (U.pullbackHom q a)).obj
          ((Scheme.Modules.pullback (U.f a)).obj F) ⟶
        (Scheme.Modules.pullback (U.pullbackHom q a)).obj
          ((Scheme.Modules.pullback (U.f a)).obj G),
        chartOrdinaryMapRecovery q p q₀ w U a
          ((Scheme.Modules.pullback (U.f a)).obj F)
          ((Scheme.Modules.pullback (U.f a)).obj G) ψ s →
        let tq := Scheme.Modules.openCoverTensorPullbackComparison q U a
        let r := tq.inv.app F ≫ s ≫ tq.hom.app G
        let tp := Scheme.Modules.openCoverTensorPullbackComparison p Uk a
        let e := Scheme.Modules.tensorPullbackCompositionIso p q q₀ w
        tp.inv.app ((Scheme.Modules.tensorPullback q).obj F) ≫
            (Scheme.Modules.pullback (Uk.pullbackHom p a)).map r ≫
            tp.hom.app ((Scheme.Modules.tensorPullback q).obj G) =
          (Scheme.Modules.pullback (V.f a)).map
            (e.inv.app F ≫ φ ≫ e.hom.app G) := by
  -- Prove the morphism calculation with abstract functors and the exact target expression.
  dsimp only
  intro s hs
  delta chartOrdinaryMapRecovery at hs
  extract_lets (config := { onlyGivenNames := true }) Uk V W v d at hs
  let Q : (Uk.X a).Modules ⥤ (V.X a).Modules :=
    Scheme.Modules.pullback (Uk.pullbackHom p a)
  let P : Z.Modules ⥤ (V.X a).Modules := Scheme.Modules.pullback (V.f a)
  let R : (W.X a).Modules ⥤ (V.X a).Modules := Scheme.Modules.pullback v
  let b : Scheme.Modules.pullback (W.f a) ⋙ R ≅ P := Scheme.Modules.pullbackComp v (W.f a) ≪≫
    Scheme.Modules.pullbackCongr
      (show v ≫ W.f a = V.f a from pullback.lift_fst _ _ _)
  let tq : Scheme.Modules.pullback (U.f a) ⋙
      Scheme.Modules.pullback (U.pullbackHom q a) ≅
      Scheme.Modules.tensorPullback q ⋙ Scheme.Modules.pullback (Uk.f a) :=
    Scheme.Modules.openCoverTensorPullbackComparison q U a
  let tp : Scheme.Modules.pullback (Uk.f a) ⋙ Q ≅
      Scheme.Modules.tensorPullback p ⋙ P := Scheme.Modules.openCoverTensorPullbackComparison p Uk a
  let t₀ : Scheme.Modules.pullback (U.f a) ⋙
      Scheme.Modules.pullback (U.pullbackHom q₀ a) ≅
      Scheme.Modules.tensorPullback q₀ ⋙ Scheme.Modules.pullback (W.f a) :=
    Scheme.Modules.openCoverTensorPullbackComparison q₀ U a
  let e : Scheme.Modules.tensorPullback q₀ ≅
      Scheme.Modules.tensorPullback q ⋙ Scheme.Modules.tensorPullback p :=
    Scheme.Modules.tensorPullbackCompositionIso p q q₀ w
  change tp.inv.app ((Scheme.Modules.tensorPullback q).obj F) ≫
      Q.map (tq.inv.app F ≫ s ≫ tq.hom.app G) ≫
      tp.hom.app ((Scheme.Modules.tensorPullback q).obj G) =
    P.map (e.inv.app F ≫ φ ≫ e.hom.app G)
  have hcoh (H : X.Modules) : Q.map (tq.hom.app H) ≫
      tp.hom.app ((Scheme.Modules.tensorPullback q).obj H) =
      d.inv.app ((Scheme.Modules.pullback (U.f a)).obj H) ≫ R.map (t₀.hom.app H) ≫
      b.hom.app ((Scheme.Modules.tensorPullback q₀).obj H) ≫ P.map (e.hom.app H) :=
    chart_tensor_pullback_comparison_coherence q p q₀ w U a H v
      (pullback.lift_fst _ _ _) (pullback.lift_snd _ _ _) d rfl b rfl
  change d.inv.app ((Scheme.Modules.pullback (U.f a)).obj F) ≫
      R.map (t₀.hom.app F ≫ (Scheme.Modules.pullback (W.f a)).map φ ≫ t₀.inv.app G) ≫
      d.hom.app ((Scheme.Modules.pullback (U.f a)).obj G) = Q.map s at hs
  clear_value d b tq tp t₀ e
  as_aux_lemma =>
    apply @comparison_transport X.Modules (U.X a).Modules (Uk.X a).Modules (W.X a).Modules
      Y.Modules Z.Modules (V.X a).Modules inferInstance inferInstance inferInstance
      inferInstance inferInstance inferInstance inferInstance (Scheme.Modules.pullback (U.f a))
      (Scheme.Modules.pullback (U.pullbackHom q a))
      (Scheme.Modules.pullback (U.pullbackHom q₀ a)) Q R
      (Scheme.Modules.tensorPullback q) (Scheme.Modules.tensorPullback p)
      (Scheme.Modules.tensorPullback q₀) (Scheme.Modules.pullback (Uk.f a))
      (Scheme.Modules.pullback (W.f a)) P tq tp t₀ e d b F G φ s
      hcoh hs


end AlgebraicGeometry
