/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.AlgebraicGeometry.AffineScheme
public import WeilConjectures.AlgebraicGeometry.Cohomology.DirectImage.Basic
public import WeilConjectures.AlgebraicGeometry.Cohomology.DirectImage.IsFlatOver
public import WeilConjectures.AlgebraicGeometry.TensorPullback
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Defs
import WeilConjectures.AlgebraicGeometry.EventuallyProper
import WeilConjectures.AlgebraicGeometry.FlatModuleOnLaterStage
import WeilConjectures.AlgebraicGeometry.RelativelyFlatModulePullback
import WeilConjectures.AlgebraicGeometry.TensorPullbackFinitePresentation
import WeilConjectures.Mathlib.AlgebraicGeometry.AffineTransitionLimit

/-! # Descent of a proper morphism and a relatively flat finitely presented sheaf

Source: Stacks Project, Tags 0A1H, 05LY and 081F.
(blueprint: lem-pc-proper-flat-single-noetherian-descent).
-/

@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry

private theorem proper_ring_stage
    {I : Type u} [Preorder I] [IsDirected I (· ≤ ·)] [Nonempty I]
    (R : I ⥤ CommRingCat.{u}) [∀ k : I, IsNoetherianRing (R.obj k)]
    (c : Cone (R.op ⋙ Scheme.Spec)) (hc : IsLimit c)
    {Z : Scheme.{u}} (f : Z ⟶ c.pt) [IsProper f]
    [LocallyOfFinitePresentation f] [QuasiCompact f] [QuasiSeparated f] :
    ∃ (i : I) (Zi : Scheme.{u}) (fi : Zi ⟶ Spec (R.obj i)) (a : Z ⟶ Zi),
      IsProper fi ∧ LocallyOfFinitePresentation fi ∧ QuasiCompact fi ∧
        QuasiSeparated fi ∧ IsPullback a f fi (c.π.app (Opposite.op i)) := by
  let D := R.op ⋙ Scheme.Spec
  have (i : Iᵒᵖ) : CompactSpace (D.obj i) := by dsimp [D]; infer_instance
  have (i : Iᵒᵖ) : QuasiSeparatedSpace (D.obj i) := by dsimp [D]; infer_instance
  have {i j : Iᵒᵖ} (t : i ⟶ j) : IsAffineHom (D.map t) := by
    dsimp [D]
    infer_instance
  obtain ⟨i, Zi, fi, hfp, hqc, hqs, a, H⟩ :=
    Scheme.exists_isPullback_of_finitePresentation hc f
  have := hfp
  have := hqc
  have := hqs
  have : CompactSpace Zi := QuasiCompact.compactSpace_of_compactSpace fi
  have : QuasiSeparatedSpace Zi := quasiSeparatedSpace_of_quasiSeparated fi
  have hs : IsProper (pullback.snd fi (c.π.app i)) := by
    rw [← H.isoPullback_inv_snd]
    infer_instance
  let ψ := pullback.map fi (c.π.app i) (𝟙 (D.obj i)) (c.π.app i)
    fi (𝟙 c.pt) (𝟙 (D.obj i)) (Category.comp_id fi)
      ((Category.comp_id _).trans (Category.id_comp _).symm)
  have hψ : IsProper ψ := by
    have he : ψ ≫ pullback.snd (𝟙 (D.obj i)) (c.π.app i) =
        pullback.snd fi (c.π.app i) := by
      dsimp [ψ]
      simp only [pullback.map, pullback.lift_snd]
      exact Category.comp_id _
    rw [← he] at hs
    exact (MorphismProperty.cancel_right_of_respectsIso @IsProper _ _).mp hs
  obtain ⟨j, hij, hj⟩ := exists_isProper_baseChange_of_isLimit D c hc i.unop
    fi (𝟙 (D.obj i)) fi (by simp) hψ
  let t := D.map (homOfLE hij).op
  let fj := pullback.snd fi t
  have hfj : IsProper fj := by
    have he :
        (pullback.map fi t (𝟙 (D.obj i)) t fi (𝟙 (D.obj (Opposite.op j)))
          (𝟙 (D.obj i)) (Category.comp_id fi) (Category.comp_id t)) ≫
            pullback.snd (𝟙 (D.obj i)) t = fj := by
      simp only [pullback.map, pullback.lift_snd]
      exact Category.comp_id _
    rw [← he]
    have := hj
    infer_instance
  let aj : Z ⟶ pullback fi t := pullback.lift a (f ≫ c.π.app (Opposite.op j)) (by
    rw [Category.assoc, c.w (homOfLE hij).op, H.w])
  have Hj : IsPullback aj f fj (c.π.app (Opposite.op j)) := by
    refine IsPullback.of_right ?_ ?_ (IsPullback.of_hasPullback fi t)
    · rw [show aj ≫ pullback.fst fi t = a from pullback.lift_fst _ _ _]
      change IsPullback a f fi (c.π.app (Opposite.op j) ≫ D.map (homOfLE hij).op)
      rw [c.w]
      exact H
    · simp only [aj, fj, pullback.lift_snd]
  exact ⟨j, pullback fi t, fj, aj, hfj, inferInstance, inferInstance,
    inferInstance, Hj⟩

private theorem flatOver_restrict
    {P Q T : Scheme.{u}} (e : P ⟶ Q) [IsOpenImmersion e]
    (b : Q ⟶ T) (M : Q.Modules) (hflat : M.IsFlatOver b) :
    ((Scheme.Modules.restrictFunctor e).obj M).IsFlatOver (e ≫ b) := by
  intro V U hU
  let U' : Q.affineOpens := ⟨e ''ᵁ U.1, U.2.image_of_isOpenImmersion e⟩
  have hU' : U'.1 ≤ b ⁻¹ᵁ V.1 :=
    (e.image_mono (show U.1 ≤ e ⁻¹ᵁ (b ⁻¹ᵁ V.1) from hU)).trans
      (e.image_preimage_le _)
  have hh := hflat V U' hU'
  convert hh using 1 <;> try rfl
  ext r m
  change (M.smul ((e.appIso U.1).inv.hom
    (((e ≫ b).appLE V.1 U.1 hU).hom r))).asHom.hom m =
      (M.smul ((b.appLE V.1 U'.1 hU').hom r)).asHom.hom m
  have he : U.1 ≤ e ⁻¹ᵁ U'.1 := (e.preimage_image_eq U.1).ge
  have hcomp := e.appLE_comp_appLE b V.1 U'.1 U.1 hU' he
  have hring : (e ≫ b).appLE V.1 U.1 hU ≫ (e.appIso U.1).inv =
      b.appLE V.1 U'.1 hU' := by
    rw [← hcomp, Category.assoc, ← Scheme.Hom.appIso_hom', Iso.hom_inv_id,
      Category.comp_id]
  exact congrArg (fun t : Γ(T, V.1) ⟶ Γ(Q, U'.1) ↦ (M.smul (t.hom r)).asHom.hom m) hring

private theorem flatOver_tensorPullback_iso
    {P Q T : Scheme.{u}} (e : P ≅ Q) (b : Q ⟶ T) (M : Q.Modules)
    (hflat : M.IsFlatOver b) :
    ((Scheme.Modules.tensorPullback e.hom).obj M).IsFlatOver (e.hom ≫ b) := by
  obtain ⟨adj⟩ := Scheme.Modules.nonempty_tensorPullbackAdjunction e.hom
  let δ := adj.leftAdjointUniq (Scheme.Modules.restrictAdjunction e.hom)
  exact (flatOver_restrict e.hom b M hflat).of_iso (δ.app M).symm

/-- Geometric Noetherian descent, with no derived category or direct-image assertion.
Source: Stacks Project, Tag 0A1H, Noetherian approximation paragraph, and Tag 081F.

Proof: Choose an affine neighbourhood V of x inside U. Write its coordinate ring as
 the filtered union of its finitely generated Z-subalgebras. Restrict f to V using
 the pullback along V.ι followed by U.ι. Descend this finitely presented morphism and
 the finite presentation of the restricted sheaf to one stage (Tag 01ZM). Enlarge
 the stage so that the descended module is flat over the base (Tag 05LY), and so that
 the descended morphism is proper (Tag 081F). Take T to be the spectrum of this stage
 ring and W its total open. Transport the descended source morphism to W.toScheme
 through the total-open isomorphism. Its source Y is Noetherian, since it is quasi-compact
 and locally of finite type over a Noetherian scheme. The original pullback is the
 base change of Y along g; its projection q gives the displayed cartesian square.
 Descent of the finite presentation gives the indicated sheaf isomorphism. For zero F
 descend the zero sheaf. Empty U has no x; empty X descends the empty source.
(blueprint: lem-pc-proper-flat-single-noetherian-descent). -/
theorem properFlat_single_noetherian_descent
    {X S : Scheme.{u}} (f : X ⟶ S)
    [IsProper f] [LocallyOfFinitePresentation f] [QuasiCompact f]
    (F : X.Modules) [F.IsFinitePresentation] (hF : F.IsFlatOver f)
    (U : S.Opens) (x : U.toScheme) :
    ∃ V : U.toScheme.Opens, x ∈ V ∧
      ∃ (T Y : Scheme.{u}) (W : T.Opens),
        IsAffine T ∧ IsCompact (W : Set T) ∧ IsNoetherian W.toScheme ∧
        IsNoetherian Y ∧ ∃ (p : Y ⟶ W.toScheme),
          IsProper p ∧ ∃ (M : Y.Modules),
            M.IsFinitePresentation ∧ M.IsFlatOver p ∧
            ∃ (g : V.toScheme ⟶ W.toScheme)
              (q : pullback f (V.ι ≫ U.ι) ⟶ Y),
              IsPullback q (pullback.snd f (V.ι ≫ U.ι)) p g ∧
              Nonempty (Scheme.Modules.tensorPullbackObj q M ≅
                Scheme.Modules.tensorPullbackObj (pullback.fst f (V.ι ≫ U.ι)) F) := by
  classical
  obtain ⟨V, hV, hx, _⟩ :=
    exists_isAffineOpen_mem_and_subset (X := U.toScheme) (x := x) (U := ⊤) (by trivial)
  let : IsAffine V.toScheme := hV
  let Z := pullback f (V.ι ≫ U.ι)
  let fV : Z ⟶ V.toScheme := pullback.snd f (V.ι ≫ U.ι)
  let Fv := Scheme.Modules.tensorPullbackObj (pullback.fst f (V.ι ≫ U.ι)) F
  let : Fv.IsFinitePresentation :=
    Scheme.Modules.isFinitePresentation_tensorPullback _ F
  have hFv : Fv.IsFlatOver fV := relativelyFlat_module_pullback f (V.ι ≫ U.ι) F hF
  let A := Γ(V.toScheme, ⊤)
  let I := {B : Subalgebra ℤ A // B.FG}
  let R := CommRingCat.fgSubalgebraDiagram A
  let cr := CommRingCat.fgSubalgebraCocone A
  have hnoeth (i : I) : IsNoetherianRing (R.obj i) := by
    let : Algebra.FiniteType ℤ i.1 := (Subalgebra.fg_iff_finiteType _).mp i.2
    exact Algebra.FiniteType.isNoetherianRing ℤ i.1
  let : ∀ i : I, IsNoetherianRing (R.obj i) := hnoeth
  let cs := Scheme.Spec.mapCone cr.op
  have hcs : IsLimit cs :=
    isLimitOfPreserves Scheme.Spec (CommRingCat.isColimitFgSubalgebraCocone A).op
  let c := cs.extend V.toScheme.isoSpec.hom
  let : IsAffine c.pt := inferInstanceAs (IsAffine V.toScheme)
  have hc : IsLimit c := IsLimit.ofIsoLimit hcs
    (Cone.extendIso cs V.toScheme.isoSpec.symm)
  obtain ⟨i, Zi, fi, a, hproper, hfp, hqc, hqs, H⟩ := proper_ring_stage R c hc fV
  let : IsProper fi := hproper
  let : LocallyOfFinitePresentation fi := hfp
  let : QuasiCompact fi := hqc
  let : QuasiSeparated fi := hqs
  let e := H.isoPullback
  let M := Scheme.Modules.tensorPullbackObj e.inv Fv
  let : M.IsFinitePresentation :=
    Scheme.Modules.isFinitePresentation_tensorPullback _ Fv
  have hM : M.IsFlatOver (pullback.snd fi (c.π.app (Opposite.op i))) := by
    have hh := flatOver_tensorPullback_iso e.symm fV Fv hFv
    change M.IsFlatOver (e.inv ≫ fV) at hh
    change M.IsFlatOver _
    rw [show e.inv ≫ fV = _ from H.isoPullback_inv_snd] at hh
    exact hh
  obtain ⟨j, hij, Mj, hjfp, hjflat, ⟨eMj⟩⟩ := exists_flat_module_on_later_stage R c hc i fi M hM
  let t := Spec.map (R.map (homOfLE hij))
  let Yj := pullback fi t
  let pj : Yj ⟶ Spec (R.obj j) := pullback.snd fi t
  let : Mj.IsFinitePresentation := hjfp
  let v : Over.mk (c.π.app (Opposite.op i)) ⟶ Over.mk t :=
    Over.homMk (c.π.app (Opposite.op j)) (c.w (homOfLE hij).op)
  let bm := baseChangeMap fi v
  let qj := e.hom ≫ bm
  have Hiso : IsPullback e.hom fV (pullback.snd fi (c.π.app (Opposite.op i)))
      (𝟙 V.toScheme) := IsPullback.of_horiz_isIso
        ⟨H.isoPullback_hom_snd.trans (Category.comp_id _).symm⟩
  have Hj : IsPullback qj fV pj (c.π.app (Opposite.op j)) := by
    change IsPullback (e.hom ≫ bm) fV pj _
    have hb := Hiso.paste_horiz (isPullback_baseChangeMap fi v)
    simpa only [bm, pj, Yj, v, Over.homMk_left, Over.mk_left, Over.mk_hom,
      Category.id_comp] using hb
  obtain ⟨ec⟩ := Scheme.Modules.nonempty_tensorPullbackComp e.hom bm
  obtain ⟨er⟩ := Scheme.Modules.nonempty_tensorPullbackComp e.hom e.inv
  obtain ⟨eu⟩ := Scheme.Modules.nonempty_tensorPullbackId Z
  let ej : Scheme.Modules.tensorPullbackObj qj Mj ≅ Fv :=
    ec.app Mj ≪≫ (Scheme.Modules.tensorPullback e.hom).mapIso eMj ≪≫
      (er.app Fv).symm ≪≫
        (eqToIso (congrArg (fun z ↦ Scheme.Modules.tensorPullbackObj z Fv)
          e.hom_inv_id)) ≪≫ eu.app Fv
  let T := Spec (R.obj j)
  let W : T.Opens := ⊤
  let : IsNoetherian T := inferInstance
  let : CompactSpace W.toScheme := T.topIso.inv.homeomorph.compactSpace
  let : IsNoetherian W.toScheme := ⟨⟩
  let Y := pullback pj T.topIso.hom
  let p : Y ⟶ W.toScheme := pullback.snd pj T.topIso.hom
  let m := Scheme.Modules.tensorPullbackObj (pullback.fst pj T.topIso.hom) Mj
  let g : V.toScheme ⟶ W.toScheme := c.π.app (Opposite.op j) ≫ T.topIso.inv
  have hg : g ≫ T.topIso.hom = c.π.app (Opposite.op j) := by
    dsimp only [g]
    rw [Category.assoc, T.topIso.inv_hom_id]
    exact Category.comp_id _
  have Houter : IsPullback qj fV pj (g ≫ T.topIso.hom) := by rw [hg]; exact Hj
  let q : Z ⟶ Y := (IsPullback.of_hasPullback pj T.topIso.hom).lift qj (fV ≫ g) (by
    exact Hj.w.trans ((Category.assoc fV g T.topIso.hom).trans
      (congrArg (fun z ↦ fV ≫ z) hg)).symm)
  have Hq : IsPullback q fV p g :=
    Houter.of_right' (IsPullback.of_hasPullback pj T.topIso.hom)
  have hq : q ≫ pullback.fst pj T.topIso.hom = qj :=
    (IsPullback.of_hasPullback pj T.topIso.hom).lift_fst _ _ _
  have : IsLocallyNoetherian Y := LocallyOfFiniteType.isLocallyNoetherian p
  have : CompactSpace Y := QuasiCompact.compactSpace_of_compactSpace p
  have : IsNoetherian Y := ⟨⟩
  obtain ⟨eq⟩ := Scheme.Modules.nonempty_tensorPullbackComp q
    (pullback.fst pj T.topIso.hom)
  refine ⟨V, hx, T, Y, W, inferInstance, ?_, inferInstance, inferInstance,
    p, inferInstance, m, Scheme.Modules.isFinitePresentation_tensorPullback _ Mj,
    relativelyFlat_module_pullback pj T.topIso.hom Mj hjflat, g, q, Hq, ?_⟩
  · simpa only [W, TopologicalSpace.Opens.coe_top] using
      (isCompact_univ : IsCompact (Set.univ : Set T))
  · exact ⟨(eq.app Mj).symm ≪≫
      eqToIso (congrArg (fun z ↦ Scheme.Modules.tensorPullbackObj z Mj) hq) ≪≫ ej⟩

end AlgebraicGeometry
