/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.AlgebraicGeometry.Morphisms.UnderlyingMap
public import Mathlib.AlgebraicGeometry.AffineScheme
public import Mathlib.AlgebraicGeometry.Noetherian
import Mathlib.CategoryTheory.Presentable.Directed
import WeilConjectures.AlgebraicGeometry.DescendFinite
import WeilConjectures.AlgebraicGeometry.DescendSurjective
import WeilConjectures.AlgebraicGeometry.IsSeparatedOfSurjectiveUniversallyClosed
import WeilConjectures.AlgebraicGeometry.Morphisms.Integral.FinitePresentationApproximation
import WeilConjectures.Mathlib.AlgebraicGeometry.AffineTransitionLimit

/-!
# Noetherian factor for a finite surjective affine morphism

This packages the approximation and descent part of the proof of Stacks Lemma 01ZT.
(blueprint: lem-weil-pbc-finite-surjective-affine-target-approximation).
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry

/-- The finite surjective affine stage obtained by Noetherian approximation.
(blueprint: lem-weil-pbc-finite-surjective-affine-target-approximation). -/
structure NoetherianAffineFactor {X Y : Scheme.{u}} (f : X ⟶ Y) where
  Z : Scheme.{u}
  q : Y ⟶ Z
  W : Scheme.{u}
  g : W ⟶ Z
  affine_q : IsAffineHom q
  noetherian_Z : AlgebraicGeometry.IsNoetherian Z
  finite_g : IsFinite g
  surjective_g : Surjective g
  affine_W : IsAffine W

-- The base change of a map to the Limits.terminal object of `Over S` has the same
-- properties as the usual second pullback projection, up to a target isomorphism.
private theorem property_over_pullback_terminal
    (P : MorphismProperty Scheme.{u}) [P.RespectsIso]
    {S T A : Scheme.{u}} (p : A ⟶ S) (q : T ⟶ S) :
    P (((Over.pullback q).map (Over.homMk p (by simp) :
      Over.mk p ⟶ Over.mk (𝟙 S))).left) ↔ P (Limits.pullback.snd p q) := by
  have he : (((Over.pullback q).map (Over.homMk p (by simp) :
      Over.mk p ⟶ Over.mk (𝟙 S))).left) ≫ Limits.pullback.snd (𝟙 S) q =
      Limits.pullback.snd p q := by
    simp
  rw [← he]
  exact (MorphismProperty.cancel_right_of_respectsIso P _ _).symm

-- Stacks 01ZT, approximation paragraphs after the reduction to finite presentation.
private theorem factor_of_finitePresentation {X Y : Scheme.{u}} (f : X ⟶ Y)
    [IsFinite f] [Surjective f] [IsAffine X]
    [CompactSpace Y] [QuasiSeparatedSpace Y] [LocallyOfFinitePresentation f] :
    Nonempty (NoetherianAffineFactor f) := by
  classical
  -- Reindex absolute Noetherian approximation by a nonempty directed order.
  obtain ⟨N⟩ := Y.nonempty_noetherianApproximation
  obtain ⟨I, horder, hdir, hne, F, hfinal⟩ := IsFiltered.exists_directed N.Iᵒᵖ
  let := horder
  let := hdir
  let := hne
  let := hfinal
  let R := F.leftOp
  let D := R ⋙ N.D
  let c := (Limits.Cone.mk Y N.π).whisker R
  have hc : Limits.IsLimit c :=
    (Functor.Initial.isLimitWhiskerEquiv R (Limits.Cone.mk Y N.π)).symm N.isLimit
  let (i : Iᵒᵖ) : CompactSpace (D.obj i) := N.compactSpace_obj (R.obj i)
  let (i : Iᵒᵖ) : QuasiSeparatedSpace (D.obj i) := by
    change QuasiSeparatedSpace (N.D.obj (R.obj i))
    infer_instance
  let {i j : Iᵒᵖ} (a : i ⟶ j) : IsAffineHom (D.map a) := N.isAffineHom_map (R.map a)
  -- Spread out the finitely presented morphism and transport its limit properties.
  obtain ⟨i₀, A, p, hp, hqc, hqs, a, H⟩ :=
    Scheme.exists_isPullback_of_finitePresentation (D := D) (c := c) hc f
  let := hp
  let := hqc
  let := hqs
  let : CompactSpace A := QuasiCompact.compactSpace_of_compactSpace p
  let : QuasiSeparatedSpace A := quasiSeparatedSpace_of_quasiSeparated p
  have hfinite : IsFinite (Limits.pullback.snd p (c.π.app i₀)) := by
    rw [← MorphismProperty.cancel_left_of_respectsIso @IsFinite H.isoPullback.hom,
      H.isoPullback_hom_snd]
    infer_instance
  have hsurj : Surjective (Limits.pullback.snd p (c.π.app i₀)) := by
    rw [← MorphismProperty.cancel_left_of_respectsIso @Surjective H.isoPullback.hom,
      H.isoPullback_hom_snd]
    infer_instance
  -- The descent lemmas use morphisms in `Over`; the target is its Limits.terminal object.
  let X₀ := Over.mk p
  let Y₀ := Over.mk (𝟙 (D.obj i₀))
  let f₀ : X₀ ⟶ Y₀ := Over.homMk p (by simp [X₀, Y₀])
  let : CompactSpace X₀.left := ‹CompactSpace A›
  let : QuasiSeparatedSpace X₀.left := ‹QuasiSeparatedSpace A›
  let : CompactSpace Y₀.left := inferInstanceAs (CompactSpace (D.obj i₀))
  let : QuasiSeparatedSpace Y₀.left := inferInstanceAs (QuasiSeparatedSpace (D.obj i₀))
  let : LocallyOfFiniteType f₀.left := inferInstanceAs (LocallyOfFiniteType p)
  let : LocallyOfFinitePresentation f₀.left := hp
  have hfinite' : IsFinite (((Over.pullback (c.π.app i₀)).map f₀).left) :=
    (property_over_pullback_terminal @IsFinite p (c.π.app i₀)).mpr hfinite
  have hsurj' : Surjective (((Over.pullback (c.π.app i₀)).map f₀).left) :=
    (property_over_pullback_terminal @Surjective p (c.π.app i₀)).mpr hsurj
  obtain ⟨i₁, hi₁, hf₁⟩ :=
    exists_isFinite_baseChange_stage D c hc i₀.unop X₀ Y₀ f₀ hfinite'
  obtain ⟨i₂, hi₂, hs₂⟩ :=
    exists_surjective_of_isLimit D c hc i₀.unop X₀ Y₀ f₀ hsurj'
  have hf₁' : IsFinite (Limits.pullback.snd p (D.map (homOfLE hi₁).op)) :=
    (property_over_pullback_terminal @IsFinite p _).mp hf₁
  have hs₂' : Surjective (Limits.pullback.snd p (D.map (homOfLE hi₂).op)) :=
    (property_over_pullback_terminal @Surjective p _).mp hs₂
  -- The source models form a limit diagram over the cofinal category of later stages.
  let B := baseChangeDiagram D p
  let bc := baseChangeCone D c p
  have hbc : Limits.IsLimit bc := isLimitBaseChangeCone D c p hc
  let : IsAffine bc.pt := (IsAffine.iff_of_isIso H.isoPullback.hom).mp inferInstance
  let (j : Over i₀) : CompactSpace (B.obj j) := by
    change CompactSpace ↥(Limits.pullback p (D.map j.hom) : Scheme.{u})
    exact QuasiCompact.compactSpace_of_compactSpace (Limits.pullback.snd p (D.map j.hom))
  let (j : Over i₀) : QuasiSeparatedSpace (B.obj j) := by
    change QuasiSeparatedSpace ↥(Limits.pullback p (D.map j.hom) : Scheme.{u})
    exact quasiSeparatedSpace_of_quasiSeparated (Limits.pullback.snd p (D.map j.hom))
  obtain ⟨j, hj⟩ := Scheme.exists_isAffine_of_isLimit B bc hbc
  -- One common upper bound preserves all three stage properties by base change.
  obtain ⟨k₁, hk₁₁, hk₁₂⟩ := exists_ge_ge i₁ i₂
  obtain ⟨k, hkk₁, hkj⟩ := exists_ge_ge k₁ j.left.unop
  have hk₁ := hk₁₁.trans hkk₁
  have hk₂ := hk₁₂.trans hkk₁
  let l : Over i₀ := Over.mk (homOfLE (hi₁.trans hk₁)).op
  let l₁ : Over i₀ := Over.mk (homOfLE hi₁).op
  let l₂ : Over i₀ := Over.mk (homOfLE hi₂).op
  let b₁ : l ⟶ l₁ := Over.homMk (homOfLE hk₁).op (by subsingleton)
  let b₂ : l ⟶ l₂ := Over.homMk (homOfLE hk₂).op (by subsingleton)
  let b₃ : l ⟶ j := Over.homMk (homOfLE hkj).op (by subsingleton)
  have hfk : IsFinite (Limits.pullback.snd p (D.map l.hom)) :=
    MorphismProperty.of_isPullback (P := @IsFinite)
      (isPullback_baseChangeDiagram_map D p b₁) hf₁'
  have hsk : Surjective (Limits.pullback.snd p (D.map l.hom)) :=
    MorphismProperty.of_isPullback (P := @Surjective)
      (isPullback_baseChangeDiagram_map D p b₂) hs₂'
  let := hj
  let : IsAffine (B.obj l) := isAffine_of_isAffineHom (B.map b₃)
  exact ⟨{
    Z := D.obj l.left
    q := c.π.app l.left
    W := B.obj l
    g := Limits.pullback.snd p (D.map l.hom)
    affine_q := isAffineHom_π_app D c hc l.left
    noetherian_Z := N.isNoetherian_obj (R.obj l.left)
    finite_g := hfk
    surjective_g := hsk
    affine_W := inferInstance }⟩

/-- A finite surjective map from an affine scheme admits a Noetherian affine stage.

Proof (the approximation portion of Stacks Lemma 01ZT):
1. The structure maps to Spec ℤ compose uniquely. Since X is affine it is quasi-compact
   and separated; surjectivity makes Y quasi-compact. Finiteness implies integrality and
   universal closedness, so separatedness descends to Y. Its closed diagonal is affine
   and quasi-compact, hence Y is quasi-separated
   [lem-weil-pbc-morphism-into-affine-scheme, lem-weil-pbc-affine-morphism-permanence,
   lem-weil-pbc-qcqs-over-affine, def-weil-surjective-morphism,
   lem-weil-pbc-finite-iff-integral-lft, pqf-lem-integral-univclosed,
   lem-weil-pbc-surjective-universally-closed-separated,
   lem-weil-pbc-closed-immersion-integral-separated-uc, definition-ind-etale-pro-etale-weakly--3].
2. Express the integral f as a directed limit of finite, finitely presented Y-schemes
   with affine transitions. These schemes are qcqs; since their limit X is affine,
   some stage is affine. Its map to Y is surjective since f factors through it.
   Replace X and f by that stage to assume finite presentation
   [lem-weil-pbc-integral-morphism-limit-of-finite, def-weil-finite-integral-morphism,
   lem-weil-pbc-affine-morphism-permanence, lem-weil-pbc-qcqs-morphism-permanence,
   lem-weil-pbc-limit-affine-stage, def-weil-surjective-morphism].
3. Approximate qcqs Y by schemes Y_i of finite type over ℤ with affine transitions,
   and reindex by a nonempty directed set. Each Y_i is Noetherian and qcqs
   [theorem-nagata-s-compactification-theorem--1, theorem-nagata-s-compactification-theorem--1,
   lem-weil-pbc-cofiltered-limit-directed-reindex, lem-weil-pbc-finite-type-over-noetherian,
   pqf-def-locnoeth, lem-weil-pbc-locally-noetherian-quasi-separated].
4. Descend f to a finitely presented g₀ : X₀ → Y₀. Restrict to the cofinal tail and
   set X_i = X₀ ×_{Y₀} Y_i. These are qcqs with affine transitions, and their limit
   is X, compatibly with f
   [proposition-jacobian-over-ground-field--1, def-sbc-locally-finite-presentation,
   def-pc-fibre-product, lem-weil-pbc-colimit-initial-full-subcategory,
   lem-weil-pbc-scheme-over-limit, lem-weil-pbc-qcqs-morphism-permanence].
5. Descend finiteness of f to some g_i; finite presentation supplies local finite type.
   All later g_i are finite by base change
   [def-sbc-locally-finite-presentation, def-weil-finite-type-morphism,
   lem-weil-pbc-descend-finite, def-pc-fibre-product,
   lem-weil-pbc-finite-morphism-permanence].
6. Descend surjectivity of f to some g_i using local finite presentation. All later
   g_i are surjective by base change. This supplies a step implicit in Stacks' proof
   [lem-weil-pbc-descend-surjective, lem-weil-pbc-surjective-base-change].
7. Since the limit X is affine, the qcqs X_i are affine for all sufficiently large i
   [def-pc-scheme, lem-weil-pbc-limit-affine-stage].
8. Choose a common upper bound of the finiteness, surjectivity and affineness
   stages. Put Z = Y_i, W = X_i and g = g_i. Then Z is Noetherian, W is affine,
   and g is finite and surjective. The limit projection q : Y → Z is affine because
   all transition maps are affine [lem-weil-pbc-limit-affine-transition]. These
   objects and properties supply the factor. No affineness of Z is used here.
(blueprint: lem-weil-pbc-finite-surjective-affine-target-approximation). -/
theorem exists_noetherian_affine_factor {X Y : Scheme.{u}} (f : X ⟶ Y)
    [IsFinite f] [Surjective f] [IsAffine X] :
    Nonempty (NoetherianAffineFactor f) := by
  classical
  let : CompactSpace Y := ⟨by
    rw [← (Surjective.surj (f := f)).range_eq]
    exact isCompact_range f.continuous⟩
  let : IsSeparated (Limits.terminal.from Y) :=
    isSeparated_of_surjective_universallyClosed (Limits.terminal.from X) (Limits.terminal.from Y)
      f (Limits.terminal.comp_from f)
  let : QuasiSeparatedSpace Y := quasiSeparatedSpace_of_quasiSeparated (Limits.terminal.from Y)
  obtain ⟨F, hF⟩ := f.exists_finiteApproximation_of_isIntegralHom
  obtain ⟨i, hi⟩ := Scheme.exists_isAffine_of_isLimit F.D (Limits.Cone.mk X F.π) F.isLimit
  let := hi
  let := hF i
  let : Surjective (F.p i) := ⟨by
    have hsurj : Function.Surjective (F.π.app i ≫ F.p i) := by
      rw [F.π_p]
      exact Surjective.surj
    exact Function.Surjective.of_comp hsurj⟩
  obtain ⟨A⟩ := factor_of_finitePresentation (F.p i)
  exact ⟨{
    Z := A.Z
    q := A.q
    W := A.W
    g := A.g
    affine_q := A.affine_q
    noetherian_Z := A.noetherian_Z
    finite_g := A.finite_g
    surjective_g := A.surjective_g
    affine_W := A.affine_W }⟩

end AlgebraicGeometry
