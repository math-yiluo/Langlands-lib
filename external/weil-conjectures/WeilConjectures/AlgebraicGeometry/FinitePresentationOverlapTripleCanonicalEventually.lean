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
import WeilConjectures.AlgebraicGeometry.Modules.FiniteDescent
import WeilConjectures.AlgebraicGeometry.FinitePresentationTestMapZeroEventually

/-! # Finite-stage canonical triple-overlap equation

Source: Stacks Project, Tag 01ZR (3), first proof by Zariski gluing.
(blueprint: lem-pc-fp-overlap-triple-canonical-eventually). -/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry

private noncomputable def canonicalPair {S A B : Scheme.{u}}
    (f : A ⟶ S) (g : B ⟶ S) : ChosenPullback f g where
  pullback := pullback f g
  p₁ := pullback.fst f g
  p₂ := pullback.snd f g
  condition := pullback.condition
  isLimit := (IsPullback.of_hasPullback f g).isLimit

private noncomputable def canonicalTriple {S A B C : Scheme.{u}}
    {f : A ⟶ S} {g : B ⟶ S} {h : C ⟶ S}
    (ab : ChosenPullback f g) (bc : ChosenPullback g h)
    (ac : ChosenPullback f h) : ChosenPullback₃ ab bc ac where
  chosenPullback := canonicalPair ab.p₂ bc.p₁
  l := {
    f := ac.isPullback.lift
      (pullback.fst ab.p₂ bc.p₁ ≫ ab.p₁)
      (pullback.snd ab.p₂ bc.p₁ ≫ bc.p₂) (by
        simp only [Category.assoc, ab.hp₁, bc.hp₂]
        rw [← ab.hp₂, ← bc.hp₁, ← Category.assoc, pullback.condition]
        simp only [Category.assoc])
    f_p₁ := ac.isPullback.lift_fst _ _ _
    f_p₂ := ac.isPullback.lift_snd _ _ _
    f_p := by rw [← ac.hp₁, ← Category.assoc, ac.isPullback.lift_fst]; simp [canonicalPair] }

private lemma pullback_finiteness {X Y : Scheme.{u}} (g : X ⟶ Y) (M : Y.Modules)
    (hfp : M.IsFinitePresentation) (hqc : M.IsQuasicoherent) :
    ((Scheme.Modules.pullback g).obj M).IsFinitePresentation ∧
      ((Scheme.Modules.pullback g).obj M).IsQuasicoherent := by
  let := hfp
  let := hqc
  exact ⟨inferInstance, inferInstance⟩

private lemma canonicalTriple_compact
    {S : Scheme.{u}} [QuasiSeparatedSpace S] (V : S.OpenCover.{u})
    [∀ x, IsAffine (V.X x)] (a b d : V.I₀) :
    CompactSpace (canonicalTriple (canonicalPair (V.f a) (V.f b))
      (canonicalPair (V.f b) (V.f d)) (canonicalPair (V.f a) (V.f d))).pullback := by
  have : QuasiCompact (V.f b) := inferInstance
  dsimp [canonicalTriple, canonicalPair, ChosenPullback₃.pullback]
  infer_instance

set_option backward.isDefEq.respectTransparency false in
private lemma triple_pull_iff
    {C : Type*} [Category C]
    {F : Pseudofunctor (LocallyDiscrete Cᵒᵖ) Cat}
    {ι : Type*} {S S' : C} {X X' : ι → C}
    {f : ∀ a, X a ⟶ S} {f' : ∀ a, X' a ⟶ S'}
    {p : S' ⟶ S} {s : ∀ a, X' a ⟶ X a}
    (w : ∀ a, s a ≫ f a = f' a ≫ p)
    (T : F.OverlapTransitions f)
    {a b d : ι} {Y Y' : C}
    (q : Y ⟶ S) (g₁ : Y ⟶ X a) (g₂ : Y ⟶ X b) (g₃ : Y ⟶ X d)
    (h₁ : g₁ ≫ f a = q) (h₂ : g₂ ≫ f b = q) (h₃ : g₃ ≫ f d = q)
    (q' : Y' ⟶ S') (g₁' : Y' ⟶ X' a) (g₂' : Y' ⟶ X' b)
    (g₃' : Y' ⟶ X' d)
    (h₁' : g₁' ≫ f' a = q') (h₂' : g₂' ≫ f' b = q')
    (h₃' : g₃' ≫ f' d = q')
    (φ : Y' ⟶ Y) (hq : φ ≫ q = q' ≫ p)
    (e₁ : φ ≫ g₁ = g₁' ≫ s a) (e₂ : φ ≫ g₂ = g₂' ≫ s b)
    (e₃ : φ ≫ g₃ = g₃' ≫ s d) :
    (T.pull (α := fun a ↦ a) w).hom q' g₁' g₂' h₁' h₂' ≫
      (T.pull (α := fun a ↦ a) w).hom q' g₂' g₃' h₂' h₃' =
      (T.pull (α := fun a ↦ a) w).hom q' g₁' g₃' h₁' h₃' ↔
    (F.map φ.op.toLoc).toFunctor.map (T.hom q g₁ g₂ h₁ h₂) ≫
      (F.map φ.op.toLoc).toFunctor.map (T.hom q g₂ g₃ h₂ h₃) =
      (F.map φ.op.toLoc).toFunctor.map (T.hom q g₁ g₃ h₁ h₃) := by
  have n₁₂ := T.pullHom_hom φ q (q' ≫ p) hq g₁ g₂ h₁ h₂
    (g₁' ≫ s a) (g₂' ≫ s b) e₁ e₂
  have n₂₃ := T.pullHom_hom φ q (q' ≫ p) hq g₂ g₃ h₂ h₃
    (g₂' ≫ s b) (g₃' ≫ s d) e₂ e₃
  have n₁₃ := T.pullHom_hom φ q (q' ≫ p) hq g₁ g₃ h₁ h₃
    (g₁' ≫ s a) (g₃' ≫ s d) e₁ e₃
  change CategoryTheory.Pseudofunctor.OverlapTransitions.pulledHom w T
    q' g₁' g₂' h₁' h₂' ≫
    CategoryTheory.Pseudofunctor.OverlapTransitions.pulledHom w T
    q' g₂' g₃' h₂' h₃' =
    CategoryTheory.Pseudofunctor.OverlapTransitions.pulledHom w T
    q' g₁' g₃' h₁' h₃' ↔ _
  dsimp only [CategoryTheory.Pseudofunctor.OverlapTransitions.pulledHom]
  rw [← n₁₂, ← n₂₃, ← n₁₃]
  dsimp only [CategoryTheory.Pseudofunctor.LocallyDiscreteOpToCat.pullHom]
  let E₁ := (Cat.Hom.toNatIso
    (F.mapComp (s a).op.toLoc g₁'.op.toLoc)).app (T.obj a)
  let E₂ := (Cat.Hom.toNatIso
    (F.mapComp (s b).op.toLoc g₂'.op.toLoc)).app (T.obj b)
  let E₃ := (Cat.Hom.toNatIso
    (F.mapComp (s d).op.toLoc g₃'.op.toLoc)).app (T.obj d)
  let D₁ := (Cat.Hom.toNatIso
    (F.mapComp' g₁.op.toLoc φ.op.toLoc
      (g₁' ≫ s a).op.toLoc (by exact congrArg (fun z ↦ z.op.toLoc) e₁))).app (T.obj a)
  let D₂ := (Cat.Hom.toNatIso
    (F.mapComp' g₂.op.toLoc φ.op.toLoc
      (g₂' ≫ s b).op.toLoc (by exact congrArg (fun z ↦ z.op.toLoc) e₂))).app (T.obj b)
  let D₃ := (Cat.Hom.toNatIso
    (F.mapComp' g₃.op.toLoc φ.op.toLoc
      (g₃' ≫ s d).op.toLoc (by exact congrArg (fun z ↦ z.op.toLoc) e₃))).app (T.obj d)
  change (E₁.inv ≫
    (D₁.hom ≫ (F.map φ.op.toLoc).toFunctor.map (T.hom q g₁ g₂ h₁ h₂) ≫ D₂.inv) ≫
      E₂.hom) ≫ (E₂.inv ≫
        (D₂.hom ≫ (F.map φ.op.toLoc).toFunctor.map (T.hom q g₂ g₃ h₂ h₃) ≫ D₃.inv) ≫
          E₃.hom) = E₁.inv ≫
    (D₁.hom ≫ (F.map φ.op.toLoc).toFunctor.map (T.hom q g₁ g₃ h₁ h₃) ≫ D₃.inv) ≫
      E₃.hom ↔ _
  constructor
  · intro hh
    have hh' := congrArg (fun z ↦ D₁.inv ≫ E₁.hom ≫ z ≫ E₃.inv ≫ D₃.hom) hh
    simpa using hh'
  · intro hh
    simpa using congrArg (fun z ↦ E₁.inv ≫ D₁.hom ≫ z ≫ D₃.inv ≫ E₃.hom) hh

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

set_option backward.isDefEq.respectTransparency false in
private lemma limit_triple_defect_zero
    {S S' Y : Scheme.{u}} (V : S.OpenCover.{u})
    (T : modulesPseudofunctor.OverlapTransitions V.f) (p : S' ⟶ S)
    (hT : (T.pull (α := fun a ↦ a) (fun a ↦ V.pullbackHom_map p a)).Coherent)
    {a b d : V.I₀} (q : Y ⟶ S)
    (g₁ : Y ⟶ V.X a) (g₂ : Y ⟶ V.X b) (g₃ : Y ⟶ V.X d)
    (h₁ : g₁ ≫ V.f a = q) (h₂ : g₂ ≫ V.f b = q) (h₃ : g₃ ≫ V.f d = q) :
    let F := (Scheme.Modules.pullback g₁).obj (T.obj a)
    let G := (Scheme.Modules.pullback g₃).obj (T.obj d)
    let δ : F ⟶ G :=
      (show F ⟶ G from T.hom q g₁ g₂ h₁ h₂ ≫ T.hom q g₂ g₃ h₂ h₃) -
      (show F ⟶ G from T.hom q g₁ g₃ h₁ h₃)
    (Scheme.Modules.pullback (pullback.fst q p)).map δ = 0 := by
  intro F G δ
  let π := pullback.fst q p
  let qLimit := pullback.snd q p
  let gLimit (x : V.I₀) (g : Y ⟶ V.X x) (hg : g ≫ V.f x = q) :
      pullback q p ⟶ (V.pullback₁ p).X x :=
    pullback.lift qLimit (π ≫ g) (by
      dsimp only [qLimit, π]
      rw [Category.assoc, hg, pullback.condition])
  have gLimit_f (x : V.I₀) (g : Y ⟶ V.X x) (hg : g ≫ V.f x = q) :
      gLimit x g hg ≫ (V.pullback₁ p).f x = qLimit :=
    pullback.lift_fst _ _ _
  have gLimit_s (x : V.I₀) (g : Y ⟶ V.X x) (hg : g ≫ V.f x = q) :
      gLimit x g hg ≫ V.pullbackHom p x = π ≫ g :=
    pullback.lift_snd _ _ _
  have h := hT.hom_comp qLimit (gLimit a g₁ h₁) (gLimit b g₂ h₂)
    (gLimit d g₃ h₃) (gLimit_f a g₁ h₁) (gLimit_f b g₂ h₂) (gLimit_f d g₃ h₃)
  have hz := (triple_pull_iff (fun x ↦ V.pullbackHom_map p x) T
    q g₁ g₂ g₃ h₁ h₂ h₃ qLimit (gLimit a g₁ h₁) (gLimit b g₂ h₂)
    (gLimit d g₃ h₃) (gLimit_f a g₁ h₁) (gLimit_f b g₂ h₂) (gLimit_f d g₃ h₃) π
    (show π ≫ q = qLimit ≫ p from pullback.condition)
    (gLimit_s a g₁ h₁).symm (gLimit_s b g₂ h₂).symm (gLimit_s d g₃ h₃).symm).mp h
  dsimp only [δ]
  rw [Functor.map_sub, sub_eq_zero]
  exact ((Scheme.Modules.pullback π).map_comp _ _).trans hz

set_option backward.isDefEq.respectTransparency false in
-- Keep the original, unused existential proof binder in the theorem signature.
set_option linter.unusedVariables false in
/--
Finite-stage vanishing of the canonical triple-overlap defect.  This is the
finite-presentation zero-map descent part of the persistent overlap argument;
the remaining transport to arbitrary chosen pullbacks is a separate theorem.
Source: Stacks Project, Tag 01ZR, clause (3).
(blueprint: lem-pc-fp-overlap-triple-canonical-eventually).
-/
theorem finitePresentation_overlap_triple_canonical_eventually
    {I : Type u} [Preorder I] [IsDirected I (· ≤ ·)]
    (R : I ⥤ CommRingCat.{u})
    (c : Cone (R.op ⋙ Scheme.Spec)) (hc : IsLimit c) [IsAffine c.pt]
    (i : I) {Xi : Scheme.{u}} (f : Xi ⟶ Spec (R.obj i))
    [LocallyOfFinitePresentation f] [QuasiCompact f] [QuasiSeparated f]
    (j : I) (hij : i ≤ j)
    (U : (pullback f (Spec.map (R.map (homOfLE hij)))).OpenCover.{u})
    [Finite U.I₀] [∀ a, IsAffine (U.X a)]
    (N : (a : U.I₀) → (U.X a).Modules)
    (a b d : U.I₀)
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
          ∃ sq : ∀ x y, ChosenPullback (V.f x) (V.f y),
          ∃ sq₃ : ∀ x y z, ChosenPullback₃ (sq x y) (sq y z) (sq x z),
            T'.hom (sq₃ a b d).p (sq₃ a b d).p₁ (sq₃ a b d).p₂
                (sq₃ a b d).w₁ (sq₃ a b d).w₂ ≫
              T'.hom (sq₃ a b d).p (sq₃ a b d).p₂ (sq₃ a b d).p₃
                (sq₃ a b d).w₂ (sq₃ a b d).w₃ =
              T'.hom (sq₃ a b d).p (sq₃ a b d).p₁ (sq₃ a b d).p₃
                (sq₃ a b d).w₁ (sq₃ a b d).w₃ := by
  classical
  intro k hjk q₀ V₀ p₀ T he hT
  let sq : ∀ x y, ChosenPullback (V₀.f x) (V₀.f y) :=
    fun x y ↦ canonicalPair (V₀.f x) (V₀.f y)
  let sq₃ : ∀ x y z, ChosenPullback₃ (sq x y) (sq y z) (sq x z) :=
    fun x y z ↦ canonicalTriple (sq x y) (sq y z) (sq x z)
  let C := sq₃ a b d
  have hfp (x : U.I₀) : (T.obj x : (V₀.X x).Modules).IsFinitePresentation := by
    obtain ⟨e⟩ := he x
    let := hN x
    exact Scheme.Modules.isFinitePresentation_of_iso e.symm
  have hqc (x : U.I₀) : (T.obj x : (V₀.X x).Modules).IsQuasicoherent := by
    obtain ⟨e⟩ := he x
    let := hNq x
    exact (SheafOfModules.isQuasicoherent (V₀.X x).ringCatSheaf).prop_of_iso
      e.symm inferInstance
  let F := (Scheme.Modules.pullback C.p₁).obj (T.obj a)
  let G := (Scheme.Modules.pullback C.p₃).obj (T.obj d)
  let δ : F ⟶ G :=
    (show F ⟶ G from
      T.hom C.p C.p₁ C.p₂ C.w₁ C.w₂ ≫ T.hom C.p C.p₂ C.p₃ C.w₂ C.w₃) -
    (show F ⟶ G from T.hom C.p C.p₁ C.p₃ C.w₁ C.w₃)
  have hF := pullback_finiteness C.p₁ (T.obj a) (hfp a) (hqc a)
  have hG := pullback_finiteness C.p₃ (T.obj d) (hfp d) (hqc d)
  have : QuasiSeparatedSpace
      (pullback f (Spec.map (R.map (homOfLE hij))) : Scheme.{u}) :=
    quasiSeparatedSpace_of_quasiSeparated
      (pullback.snd f (Spec.map (R.map (homOfLE hij))))
  have : IsAffineHom q₀ := by
    dsimp only [q₀, overlapStageMap]
    exact MorphismProperty.of_isPullback
      (isPullback_baseChangeMap f _).flip
      (by change IsAffineHom (Spec.map (R.map (homOfLE hjk))); infer_instance)
  have affine (x : U.I₀) : IsAffine (V₀.X x) := by
    change IsAffine (pullback q₀ (U.f x))
    infer_instance
  have : QuasiSeparatedSpace
      (pullback f (Spec.map (R.map (homOfLE (hij.trans hjk)))) : Scheme.{u}) :=
    quasiSeparatedSpace_of_quasiSeparated
      (pullback.snd f (Spec.map (R.map (homOfLE (hij.trans hjk)))))
  have : ∀ x, IsAffine (V₀.X x) := affine
  have : CompactSpace C.pullback := canonicalTriple_compact V₀ a b d
  have : QuasiCompact (C.p ≫ pullback.snd f
      (Spec.map (R.map (homOfLE (hij.trans hjk))))) := inferInstance
  have hδ : (Scheme.Modules.pullback (pullback.fst C.p p₀)).map δ = 0 :=
    limit_triple_defect_zero V₀ T p₀ hT C.p C.p₁ C.p₂ C.p₃ C.w₁ C.w₂ C.w₃
  obtain ⟨l, hkl, hl⟩ := finitePresentation_test_map_zero_eventually
    R c hc i f k (hij.trans hjk) C.p F G hF.1 hF.2 hG.1 hG.2 δ hδ
  refine ⟨l, hkl, ?_⟩
  intro m hkm hlm q V r s T'
  let sq' : ∀ x y, ChosenPullback (V.f x) (V.f y) :=
    fun x y ↦ canonicalPair (V.f x) (V.f y)
  let sq₃' : ∀ x y z, ChosenPullback₃ (sq' x y) (sq' y z) (sq' x z) :=
    fun x y z ↦ canonicalTriple (sq' x y) (sq' y z) (sq' x z)
  refine ⟨sq', sq₃', ?_⟩
  let D := sq₃' a b d
  obtain ⟨φ, e₁, e₂, e₃⟩ := C.exists_lift
    (D.p₁ ≫ s a) (D.p₂ ≫ s b) (D.p₃ ≫ s d) (D.p ≫ r)
    (by rw [Category.assoc, overlapRefinementHom_map, ← Category.assoc, D.w₁])
    (by rw [Category.assoc, overlapRefinementHom_map, ← Category.assoc, D.w₂])
    (by rw [Category.assoc, overlapRefinementHom_map, ← Category.assoc, D.w₃])
  have hφ : φ ≫ C.p = D.p ≫ r := by
    rw [← C.w₁, ← Category.assoc, e₁, Category.assoc,
      overlapRefinementHom_map, ← Category.assoc, D.w₁]
  apply (triple_pull_iff (fun x ↦ overlapRefinementHom_map U q₀ q r
      (overlapStageMap_comp R f hij hjk hkm) x) T
    C.p C.p₁ C.p₂ C.p₃ C.w₁ C.w₂ C.w₃
    D.p D.p₁ D.p₂ D.p₃ D.w₁ D.w₂ D.w₃ φ hφ e₁ e₂ e₃).mpr
  have hz : (Scheme.Modules.pullback φ).map δ = 0 := by
    let rl := overlapStageMap R f (hij.trans hjk) hkl
    let rlm := overlapStageMap R f (hij.trans (hjk.trans hkl)) hlm
    let ψ : D.pullback ⟶ pullback C.p rl :=
      pullback.lift φ (D.p ≫ rlm) (by
        rw [Category.assoc, overlapStageMap_comp]; exact hφ)
    have hψ : ψ ≫ pullback.fst C.p rl = φ := pullback.lift_fst _ _ _
    exact pullback_map_zero_of_comp ψ (pullback.fst C.p rl) φ hψ δ hl
  dsimp only [δ] at hz
  rw [Functor.map_sub, sub_eq_zero] at hz
  exact ((Scheme.Modules.pullback φ).map_comp _ _).symm.trans hz

end AlgebraicGeometry
