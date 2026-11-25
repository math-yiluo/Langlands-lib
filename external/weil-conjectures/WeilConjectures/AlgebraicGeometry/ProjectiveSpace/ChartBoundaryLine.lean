/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.ProjectiveSpace.ChartBoundary
public import WeilConjectures.AlgebraicGeometry.ProjectiveSpace.Charts
public import WeilConjectures.AlgebraicGeometry.ProjectiveSpace.Spreading
public import WeilConjectures.AlgebraicGeometry.ProjectiveSpace.LineOver
public import WeilConjectures.AlgebraicGeometry.ProjectiveSpace.LinearProjection
public import WeilConjectures.AlgebraicGeometry.AffineSpace.ZeroSection
public import WeilConjectures.Compactification.AffineCharts
public import WeilConjectures.Compactification.ProjectiveSpace
public import WeilConjectures.Mathlib.AlgebraicGeometry.IdealSheaf.Functorial

/-!
# The section at infinity of the projective line `ℙ(Option n; S)`

For the projective line `ℙ¹_B = ℙ(Option (ULift (Fin 1)); B)` with homogeneous coordinates
`T_∞ = T_none` and `T₀ = T_(some 0)`, the zero locus `Z` of `s = T_∞ / T₀` in the chart
`V = D₊(T₀)` is the section at infinity (`AlgebraicGeometry.ProjectiveSpace.lineInfinityι`, a
case of `AlgebraicGeometry.ProjectiveSpace.chartBoundaryι`). This file records:

* the chart `𝔸¹_B ≅ V ⊆ ℙ¹_B`, `z ↦ [z : 1]` in the coordinates `(T_∞, T₀)`
  (`AlgebraicGeometry.ProjectiveSpace.lineInfinityChart`), which pulls `s` back to the
  coordinate `z`;
* `Z ⟶ ℙ¹_B ⟶ B` is an isomorphism;
* `Z` is the complement of the standard chart `𝔸¹_B ⟶ ℙ¹_B` onto `D₊(T_∞)`
  (`AlgebraicGeometry.AffineSpace.toRelativeProjectiveSpace`);
* the section at infinity and the chart at infinity are compatible with base change.
-/

@[expose] public section

universe u

open CategoryTheory Limits

noncomputable section

namespace AlgebraicGeometry.ProjectiveSpace

variable (B : Scheme.{u})

/-- The standard open `D₊(T₀)` of `ℙ(Option (ULift (Fin 1)); B)`, the chart at infinity. -/
abbrev lineInfinityOpen : ℙ(Option (ULift.{u} (Fin 1)); B).Opens :=
  standardOpen (Option (ULift.{u} (Fin 1))) B (some ⟨0⟩)

/-- The coordinate `s = T_∞ / T₀` of the chart at infinity, as a global function on it. -/
abbrev lineInfinityCoord : Γ((lineInfinityOpen B).toScheme, ⊤) :=
  (lineInfinityOpen B).topIso.inv (coordRatio (Option (ULift.{u} (Fin 1))) B (some ⟨0⟩) none)

/-- The section at infinity: the zero locus of `T_∞ / T₀` in the chart `D₊(T₀)`. -/
abbrev lineInfinity : Scheme.{u} :=
  (lineInfinityOpen B).toScheme.zeroLocusSubscheme {lineInfinityCoord B}

/-- The inclusion of the section at infinity into `ℙ(Option (ULift (Fin 1)); B)`. -/
abbrev lineInfinityι : lineInfinity B ⟶ ℙ(Option (ULift.{u} (Fin 1)); B) :=
  chartBoundaryι B (some (⟨0⟩ : ULift.{u} (Fin 1))) none

/-- The homogeneous coordinates `[b : 1]` on `ℙ(Option (ULift (Fin 1)); X)`, with `b` at `none`
and `1` at `some 0`. -/
def lineSections {X : Scheme.{u}} (b : Γ(X, ⊤)) : Option (ULift.{u} (Fin 1)) → Γ(X, ⊤) :=
  fun o ↦ o.elim b fun _ ↦ 1

@[simp]
lemma lineSections_none {X : Scheme.{u}} (b : Γ(X, ⊤)) : lineSections b none = b := rfl

@[simp]
lemma lineSections_some {X : Scheme.{u}} (b : Γ(X, ⊤)) (a : ULift.{u} (Fin 1)) :
    lineSections b (some a) = 1 := rfl

/-- The sections `[b : 1]` generate the unit ideal. -/
lemma span_range_lineSections {X : Scheme.{u}} (b : Γ(X, ⊤)) :
    Ideal.span (Set.range (lineSections b)) = ⊤ :=
  Ideal.eq_top_of_isUnit_mem _ (Ideal.subset_span ⟨some ⟨0⟩, rfl⟩) isUnit_one

/-- The coordinates of the chart `D₊(T_(some 0))` of `ℙ(Option (ULift (Fin 1)); B)` are indexed
by a singleton. -/
instance subsingleton_ne_some_zero :
    Subsingleton {j : Option (ULift.{u} (Fin 1)) // j ≠ some ⟨0⟩} := by
  refine ⟨fun ⟨a, ha⟩ ⟨b, hb⟩ ↦ Subtype.ext ?_⟩
  have key (c : Option (ULift.{u} (Fin 1))) (hc : c ≠ some ⟨0⟩) : c = none := by
    cases c with
    | none => rfl
    | some x => exact absurd (congrArg some (Subsingleton.elim x _)) hc
  exact (key a ha).trans (key b hb).symm

instance : IsIso (AffineSpace.reindex (fun _ : {j : Option (ULift.{u} (Fin 1)) // j ≠ some ⟨0⟩} ↦
    (⟨0⟩ : ULift.{u} (Fin 1))) B) := by
  refine ⟨AffineSpace.reindex (fun _ ↦ ⟨none, by simp⟩) B, ?_, ?_⟩ <;>
    refine AffineSpace.hom_ext (by simp [AffineSpace.reindex_over]) fun i ↦ ?_ <;>
    rw [Scheme.Hom.comp_appTop, CommRingCat.comp_apply, AffineSpace.reindex_appTop_coord,
      AffineSpace.reindex_appTop_coord, Scheme.Hom.id_appTop, CommRingCat.id_apply] <;>
    exact congrArg _ (Subsingleton.elim _ _)

/-- **The chart at infinity of the projective line** `ℙ(Option (ULift (Fin 1)); B)`: the open
immersion `𝔸¹_B ⟶ ℙ¹_B` onto the standard open `D₊(T_(some 0))`, through the chart isomorphism
`AlgebraicGeometry.ProjectiveSpace.standardOpenIso`. In homogeneous coordinates it is
`z ↦ [z : 1]` (`AlgebraicGeometry.ProjectiveSpace.lineInfinityChart_eq_homOfSections`). -/
def lineInfinityChart : 𝔸(ULift.{u} (Fin 1); B) ⟶ ℙ(Option (ULift.{u} (Fin 1)); B) :=
  AffineSpace.reindex (fun _ : {j : Option (ULift.{u} (Fin 1)) // j ≠ some ⟨0⟩} ↦
      (⟨0⟩ : ULift.{u} (Fin 1))) B ≫
    (standardOpenIso (Option (ULift.{u} (Fin 1))) B (some ⟨0⟩)).inv ≫ (lineInfinityOpen B).ι

/-- The chart at infinity as an isomorphism onto the standard open `D₊(T_(some 0))`. -/
def lineInfinityChartToOpen : 𝔸(ULift.{u} (Fin 1); B) ⟶ (lineInfinityOpen B).toScheme :=
  AffineSpace.reindex (fun _ : {j : Option (ULift.{u} (Fin 1)) // j ≠ some ⟨0⟩} ↦
      (⟨0⟩ : ULift.{u} (Fin 1))) B ≫
    (standardOpenIso (Option (ULift.{u} (Fin 1))) B (some ⟨0⟩)).inv

instance : IsIso (lineInfinityChartToOpen B) := by
  rw [lineInfinityChartToOpen]
  infer_instance

@[reassoc (attr := simp)]
lemma lineInfinityChartToOpen_ι :
    lineInfinityChartToOpen B ≫ (lineInfinityOpen B).ι = lineInfinityChart B :=
  Category.assoc _ _ _

instance : IsOpenImmersion (lineInfinityChart B) := by
  rw [lineInfinityChart]
  infer_instance

@[reassoc (attr := simp)]
lemma lineInfinityChart_over :
    lineInfinityChart B ≫ ℙ(Option (ULift.{u} (Fin 1)); B) ↘ B =
      𝔸(ULift.{u} (Fin 1); B) ↘ B := by
  rw [lineInfinityChart, Category.assoc, Category.assoc, standardOpenIso_inv_ι_over,
    AffineSpace.reindex_over]

variable {B} in
/-- The point `z = b` of the chart at infinity is the point `[b : 1]` of `ℙ¹_B`. -/
lemma homOfVector_comp_lineInfinityChart {X : Scheme.{u}} (g : X ⟶ B) (b : Γ(X, ⊤)) :
    AffineSpace.homOfVector g (fun _ ↦ b) ≫ lineInfinityChart B =
      homOfSections g (lineSections b) (span_range_lineSections b) := by
  have := Scheme.Opens.isIso_ι_of_eq_top
    (X.basicOpen_of_isUnit (f := lineSections b (some ⟨0⟩)) isUnit_one)
  rw [← cancel_epi (X.basicOpen (lineSections b (some ⟨0⟩))).ι,
    ← Scheme.Hom.resLE_comp_ι (homOfSections g (lineSections b) (span_range_lineSections b))
      (homOfSections_preimage_standardOpen g _ (span_range_lineSections b) (some ⟨0⟩)).ge,
    ← Iso.hom_inv_id_assoc (standardOpenIso (Option (ULift.{u} (Fin 1))) B (some ⟨0⟩))
      (Scheme.Opens.ι _),
    reassoc_of% homOfSections_resLE_standardOpenIso_hom, lineInfinityChart]
  simp only [← Category.assoc]
  congr 2
  refine AffineSpace.hom_ext (by simp [AffineSpace.reindex_over]) fun j ↦ ?_
  rw [AffineSpace.homOfVector_appTop_coord, Scheme.Hom.comp_appTop, Scheme.Hom.comp_appTop,
    CommRingCat.comp_apply, CommRingCat.comp_apply, AffineSpace.reindex_appTop_coord,
    AffineSpace.homOfVector_appTop_coord]
  obtain rfl : j = ⟨none, by simp⟩ := Subsingleton.elim _ _
  exact X.eq_divBasicOpen (by rw [lineSections_some, map_one, mul_one]; rfl)

/-- The coordinate `𝔸¹_B ⟶ 𝔸¹_B` is the identity. -/
lemma homOfVector_over_coord_uLift :
    AffineSpace.homOfVector (𝔸(ULift.{u} (Fin 1); B) ↘ B)
        (fun _ ↦ AffineSpace.coord B (ULift.up 0)) = 𝟙 _ := by
  refine AffineSpace.hom_ext (by simp) fun i ↦ ?_
  rw [AffineSpace.homOfVector_appTop_coord, Subsingleton.elim i (ULift.up 0)]
  simp

/-- The chart at infinity is `z ↦ [z : 1]`. -/
lemma lineInfinityChart_eq_homOfSections :
    lineInfinityChart B = homOfSections (𝔸(ULift.{u} (Fin 1); B) ↘ B)
      (lineSections (AffineSpace.coord B (ULift.up 0))) (span_range_lineSections _) := by
  rw [← homOfVector_comp_lineInfinityChart, homOfVector_over_coord_uLift, Category.id_comp]

/-- The chart at infinity pulls the ratio `T_∞ / T₀` back to the coordinate of `𝔸¹_B`. -/
lemma lineInfinityChart_appLE_coordRatio (e) :
    (lineInfinityChart B).appLE (lineInfinityOpen B) ⊤ e
      (coordRatio (Option (ULift.{u} (Fin 1))) B (some ⟨0⟩) none) =
        AffineSpace.coord B (ULift.up 0) := by
  have h := homOfSections_appLE_coordRatio (𝔸(ULift.{u} (Fin 1); B) ↘ B)
    (lineSections (AffineSpace.coord B (ULift.up 0))) (span_range_lineSections _)
    (lineSections_some _ ⟨0⟩) none
  revert e
  rw [lineInfinityChart_eq_homOfSections]
  exact h

private lemma appLE_eq_of_eq {X Y : Scheme.{u}} {f g : X ⟶ Y} (h : f = g) (U V e) :
    f.appLE U V e = g.appLE U V (h ▸ e) := by
  subst h
  rfl

/-- For a morphism `f : Y ⟶ U` to an open subscheme `U ⊆ X`, pulling back a function on `U`
along `f` is pulling it back along `f ≫ U.ι`. -/
lemma _root_.AlgebraicGeometry.Scheme.Hom.appTop_topIso_inv {X Y : Scheme.{u}} {U : X.Opens}
    (f : Y ⟶ U.toScheme) (x : Γ(X, U)) :
    f.appTop (U.topIso.inv x) = (f ≫ U.ι).appLE U ⊤ (by
      rw [Scheme.Hom.comp_preimage]
      exact fun y _ ↦ (f y).2) x := by
  have key (W : U.toScheme.Opens) (hW : W = ⊤) (e' : ⊤ ≤ f ⁻¹ᵁ W) :
      f.appLE W ⊤ e' = U.toScheme.presheaf.map (eqToHom hW.symm).op ≫ f.appTop := by
    subst hW
    rw [eqToHom_refl, op_id, CategoryTheory.Functor.map_id, Category.id_comp, Scheme.Hom.appTop,
      Scheme.Hom.app_eq_appLE]
    rfl
  rw [Scheme.Hom.comp_appLE, key _ U.ι_preimage_self, ← Category.assoc, CommRingCat.comp_apply]
  congr 1
  simp only [Scheme.Opens.ι_app, Scheme.Opens.topIso_inv, Scheme.Opens.toScheme_presheaf_map,
    ← Functor.map_comp]
  rfl

/-- The isomorphism `𝔸¹_B ≅ D₊(T_(some 0))` pulls `T_∞ / T₀` back to the coordinate. -/
lemma lineInfinityChartToOpen_appTop :
    (lineInfinityChartToOpen B).appTop (lineInfinityCoord B) =
      AffineSpace.coord B (ULift.up 0) := by
  rw [lineInfinityCoord, Scheme.Hom.appTop_topIso_inv,
    appLE_eq_of_eq (lineInfinityChartToOpen_ι B), lineInfinityChart_appLE_coordRatio]

variable {B} in
/-- The chart at infinity is compatible with base change. -/
@[reassoc]
lemma map_comp_lineInfinityChart {B' : Scheme.{u}} (g : B' ⟶ B) :
    AffineSpace.map (ULift.{u} (Fin 1)) g ≫ lineInfinityChart B =
      lineInfinityChart B' ≫ map (Option (ULift.{u} (Fin 1))) g := by
  rw [lineInfinityChart_eq_homOfSections, lineInfinityChart_eq_homOfSections, comp_homOfSections,
    homOfSections_map]
  refine homOfSections_congr (AffineSpace.map_over g) (funext fun o ↦ ?_)
  cases o with
  | none => simp
  | some a => simp

/-- Read through the chart at infinity, the section at infinity is the zero section of `𝔸¹_B`:
the zero locus of the coordinate is the base change of the section at infinity along the chart,
by an isomorphism. -/
lemma exists_isIso_isPullback_lineInfinityChart :
    ∃ gW : 𝔸(ULift.{u} (Fin 1); B).zeroLocusSubscheme {AffineSpace.coord B (ULift.up 0)} ⟶
        lineInfinity B,
      IsIso gW ∧ IsPullback gW (𝔸(ULift.{u} (Fin 1); B).zeroLocusSubschemeι
          {AffineSpace.coord B (ULift.up 0)}) (lineInfinityι B) (lineInfinityChart B) := by
  have hs : (lineInfinityChartToOpen B).appTop '' {lineInfinityCoord B} =
      {AffineSpace.coord B (ULift.up 0)} := by
    rw [Set.image_singleton, lineInfinityChartToOpen_appTop]
  have h := Scheme.isPullback_zeroLocusSubschemeι (lineInfinityChartToOpen B) _ _ hs
  have sq : IsPullback (𝟙 (lineInfinity B)) ((lineInfinityOpen B).toScheme.zeroLocusSubschemeι
      {lineInfinityCoord B}) (lineInfinityι B) (lineInfinityOpen B).ι :=
    IsPullback.of_horiz_isIso_mono ⟨Category.id_comp _⟩
  have h' := h.paste_horiz sq
  rw [Category.comp_id, lineInfinityChartToOpen_ι] at h'
  exact ⟨_, h.isIso_fst_of_isIso, h'⟩

/-- The section at infinity `Z ⟶ ℙ¹_B ⟶ B` is an isomorphism. -/
instance isIso_lineInfinityι_comp_over :
    IsIso (lineInfinityι B ≫ ℙ(Option (ULift.{u} (Fin 1)); B) ↘ B) := by
  obtain ⟨gW, _, h⟩ := exists_isIso_isPullback_lineInfinityChart B
  have e : lineInfinityι B ≫ ℙ(Option (ULift.{u} (Fin 1)); B) ↘ B =
      inv gW ≫ (AffineSpace.zeroSectionIsoZeroLocusSubscheme (ULift.{u} (Fin 1)) B
        (s := {AffineSpace.coord B (ULift.up 0)}) Set.range_unique).inv := by
    rw [IsIso.eq_inv_comp, h.w_assoc, lineInfinityChart_over]
    rfl
  rw [e]
  infer_instance

attribute [local instance] MvPolynomial.gradedAlgebra in
/-- The section at infinity is the complement of the standard chart `𝔸¹_B ⟶ ℙ¹_B` onto
`D₊(T_∞)`. -/
lemma range_lineInfinityι_eq_compl_range_toRelativeProjectiveSpace :
    Set.range (lineInfinityι B).base =
      (Set.range (AffineSpace.toRelativeProjectiveSpace (ULift.{u} (Fin 1)) B).base)ᶜ := by
  rw [lineInfinityι, range_chartBoundaryι B
    (standardOpen_some_sup_standardOpen_none (n := ULift.{u} (Fin 1)) B (ULift.up 0))]
  congr 1
  ext z
  refine ⟨fun hz ↦ AffineSpace.mem_range_toRelativeProjectiveSpace B z hz, ?_⟩
  rintro ⟨y, rfl⟩
  have h : toProjInt _ B (AffineSpace.toRelativeProjectiveSpace (ULift.{u} (Fin 1)) B y) ∈
      (Proj.awayι (MvPolynomial.homogeneousSubmodule (Option (ULift.{u} (Fin 1))) (ULift.{u} ℤ))
        (MvPolynomial.X none) MvPolynomial.isHomogeneous_X_none Nat.one_pos).opensRange := by
    rw [← Scheme.Hom.comp_apply, AffineSpace.toRelativeProjectiveSpace_toProjInt,
      AffineSpace.toProjectiveSpaceInt, ← Category.assoc, Scheme.Hom.comp_apply]
    exact ⟨_, rfl⟩
  rw [Proj.opensRange_awayι] at h
  exact h

variable {B} in
/-- The section at infinity is compatible with base change. -/
lemma exists_isPullback_lineInfinityι_map {B' : Scheme.{u}} (g : B' ⟶ B) :
    ∃ gZ : lineInfinity B' ⟶ lineInfinity B,
      IsPullback gZ (lineInfinityι B') (lineInfinityι B) (map (Option (ULift.{u} (Fin 1))) g) := by
  have hV := map_preimage_standardOpen g (some (⟨0⟩ : ULift.{u} (Fin 1)))
  let mV := (map (Option (ULift.{u} (Fin 1))) g).resLE (lineInfinityOpen B) (lineInfinityOpen B')
    hV.ge
  have sq : IsPullback mV (lineInfinityOpen B').ι (lineInfinityOpen B).ι
      (map (Option (ULift.{u} (Fin 1))) g) :=
    IsOpenImmersion.isPullback _ _ _ _ (Scheme.Hom.resLE_comp_ι _ _).symm
      (by rw [Scheme.Opens.opensRange_ι, Scheme.Opens.opensRange_ι, hV])
  have hs : mV.appTop '' {lineInfinityCoord B} = {lineInfinityCoord B'} := by
    rw [Set.image_singleton, Set.singleton_eq_singleton_iff, Scheme.Hom.appTop,
      Scheme.Hom.resLE_app_top, CommRingCat.comp_apply, CommRingCat.comp_apply, lineInfinityCoord,
      lineInfinityCoord, Iso.inv_hom_id_apply, map_appLE_coordRatio]
  exact ⟨_, (Scheme.isPullback_zeroLocusSubschemeι mV _ _ hs).paste_vert sq⟩

variable {B} in
/-- The base change of the chart at infinity along `g : B' ⟶ B` factors through the chart
`D₊(T₀)` of `ℙ¹_B`, by a morphism pulling `T_∞ / T₀` back to the coordinate of `𝔸¹_{B'}`. -/
lemma exists_lift_lineInfinityChart_map {B' : Scheme.{u}} (g : B' ⟶ B) :
    ∃ m : 𝔸(ULift.{u} (Fin 1); B') ⟶ (lineInfinityOpen B).toScheme,
      m ≫ (lineInfinityOpen B).ι = lineInfinityChart B' ≫ map (Option (ULift.{u} (Fin 1))) g ∧
        m.appTop (lineInfinityCoord B) = AffineSpace.coord B' (ULift.up 0) := by
  refine ⟨AffineSpace.map (ULift.{u} (Fin 1)) g ≫ lineInfinityChartToOpen B, ?_, ?_⟩
  · rw [Category.assoc, lineInfinityChartToOpen_ι, map_comp_lineInfinityChart]
  · rw [Scheme.Hom.comp_appTop, CommRingCat.comp_apply, lineInfinityChartToOpen_appTop,
      AffineSpace.map_appTop_coord]

end AlgebraicGeometry.ProjectiveSpace
