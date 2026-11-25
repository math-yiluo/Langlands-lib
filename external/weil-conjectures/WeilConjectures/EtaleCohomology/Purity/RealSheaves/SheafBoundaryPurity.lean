/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.Regular
public import WeilConjectures.EtaleCohomology.Purity.RealSheaves.SheafSemicontinuity
public import WeilConjectures.Mathlib.AlgebraicGeometry.Geometrically.Connected
public import WeilConjectures.Mathlib.AlgebraicGeometry.Geometrically.Irreducible
public import WeilConjectures.WeilSheaf.DirectImageRestriction
public import WeilConjectures.WeilSheaf.Dual
public import WeilConjectures.WeilSheaf.MiddleExtension

/-!
# Boundary semicontinuity of weights: reduction to affine curves

Let `C₀` be a smooth geometrically connected curve over `k₀ = 𝔽_q`, `j : U₀ ⟶ C₀` a dense open
immersion and `ℱ` a lisse Weil sheaf on `U₀` with punctual weights at most `β`. Step 0 of the
proof of `proposition-weights-j-boundary-points--1` reduces the weight bound for `j_* ℱ` at a closed
point `s` of `C₀` to the affine case `AlgebraicGeometry.WeilSheaf.hasWeightsAtMost_directImage`: `s`
has an affine open neighbourhood `X'₀`, again a smooth geometrically connected curve (a nonempty
open of the geometrically irreducible `C₀`), and the stalk of `j_* ℱ` at `s` is that of
`j'_* (ℱ|_{U'₀})` for the restriction `j' : U'₀ = U₀ ∩ X'₀ ⟶ X'₀`
(`AlgebraicGeometry.WeilSheaf.nonempty_equiv_stalk_directImage_of_isPullback`). The general
statement is `AlgebraicGeometry.WeilSheaf.IsLisse.hasWeightsAtMost_directImage`.

## Main statements

- `AlgebraicGeometry.WeilSheaf.HasWeightsAtMost.upperStar_of_isOpenImmersion`: restriction to an
  open preserves weight bounds.
- `AlgebraicGeometry.WeilSheaf.norm_le_of_hasEigenvalue_stalk_directImage_of_isPullback`: the
  weight bound for `j_* ℱ` at a point of an affine open neighbourhood.
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry.WeilSheaf

variable {k₀ : Type u} [Field k₀] [Finite k₀] {l : ℕ} [Fact l.Prime] [Fact (ringChar k₀ ≠ l)]

omit [Finite k₀] in
/-- The residue fields of a closed point and of its image under an open immersion have the same
degree over `k₀`. -/
lemma degreeOver_eq_of_isOpenImmersion {X Y : Scheme.{u}} [X.Over (Spec (CommRingCat.of k₀))]
    [Y.Over (Spec (CommRingCat.of k₀))] (φ : X ⟶ Y) [IsOpenImmersion φ]
    [φ.IsOver (Spec (CommRingCat.of k₀))] (z : X) :
    (X ↘ Spec (CommRingCat.of k₀)).degreeOver z =
      (Y ↘ Spec (CommRingCat.of k₀)).degreeOver (φ.base z) := by
  rw [← Scheme.Hom.degreeOver_comp_of_isIso φ (Y ↘ Spec (CommRingCat.of k₀)) z, comp_over φ]

/-- **Restriction to an open preserves weight bounds.** If `F` has weights at most `w`, so has
its pullback along an open immersion `φ`: the stalk of `φ^* F` at a closed point `z` is that of
`F` at `φ z`, a point of the same degree. -/
theorem HasWeightsAtMost.upperStar_of_isOpenImmersion {ι : PadicAlgCl l →+* ℂ} {X Y : Scheme.{u}}
    [X.Over (Spec (CommRingCat.of k₀))] [Y.Over (Spec (CommRingCat.of k₀))] (φ : X ⟶ Y)
    [IsOpenImmersion φ] [φ.IsOver (Spec (CommRingCat.of k₀))] {F : WeilSheaf k₀ l Y} {w : ℝ}
    (hF : F.HasWeightsAtMost ι w) : ((WeilSheaf.upperStar φ).obj F).HasWeightsAtMost ι w := by
  intro z α hα
  have hdeg := degreeOver_eq_of_isOpenImmersion (k₀ := k₀) φ z.1
  obtain ⟨e⟩ := nonempty_equiv_stalk_upperStar φ F z
    ⟨φ.base z.1, Scheme.Hom.map_mem_finitePoints φ z.2⟩ rfl hdeg
  have h := hF _ α (e.hasEigenvalue hα)
  rw [Scheme.Hom.residueCard] at h
  rwa [Scheme.Hom.residueCard, hdeg]

section Semicontinuity

variable {C : Scheme.{u}} [C.Over (Spec (CommRingCat.of k₀))]
  [SmoothOfRelativeDimension 1 (C ↘ Spec (CommRingCat.of k₀))]
  {U : Scheme.{u}} [U.Over (Spec (CommRingCat.of k₀))] (j : U ⟶ C) [IsOpenImmersion j]
  [QuasiCompact j] [j.IsOver (Spec (CommRingCat.of k₀))]
  (ι : PadicAlgCl l →+* ℂ)

/-- A smooth curve `C₀` is locally of finite type over `k₀`. -/
local instance locallyOfFiniteType_boundaryPurity :
    LocallyOfFiniteType (C ↘ Spec (CommRingCat.of k₀)) :=
  haveI := SmoothOfRelativeDimension.smooth 1 (C ↘ Spec (CommRingCat.of k₀))
  inferInstance

/-- Step 0 of `proposition-weights-j-boundary-points--1`, abstractly: if a closed point `x` of `C₀`
lies in the image of an open immersion `i : X'₀ ⟶ C₀` from a smooth geometrically connected affine
curve, then the eigenvalues of the local Frobenius of `j_* ℱ` at `x` satisfy the weight bound,
by the affine case applied to the restriction `j' : U'₀ ⟶ X'₀` of `j`. -/
theorem norm_le_of_hasEigenvalue_stalk_directImage_of_isPullback {X' U' : Scheme.{u}}
    [X'.Over (Spec (CommRingCat.of k₀))] [U'.Over (Spec (CommRingCat.of k₀))] [IsAffine X']
    [SmoothOfRelativeDimension 1 (X' ↘ Spec (CommRingCat.of k₀))]
    [GeometricallyConnected (X' ↘ Spec (CommRingCat.of k₀))]
    {i : X' ⟶ C} {j' : U' ⟶ X'} {i' : U' ⟶ U}
    [IsOpenImmersion i] [QuasiCompact i] [i.IsOver (Spec (CommRingCat.of k₀))]
    [IsOpenImmersion j'] [QuasiCompact j'] [j'.IsOver (Spec (CommRingCat.of k₀))] [IsDominant j']
    [IsOpenImmersion i'] [QuasiCompact i'] [i'.IsOver (Spec (CommRingCat.of k₀))]
    (h : IsPullback j' i' i j) {F : WeilSheaf k₀ l U} (hF : F.IsLisse) {β : ℝ}
    (hw : F.HasWeightsAtMost ι β) (y : X'.finitePoints) (x : C.finitePoints)
    (hyx : i.base y.1 = x.1) {α : PadicAlgCl l}
    (hα : (((directImage j).obj F).stalk x).frobeniusEnd.HasEigenvalue α) :
    ‖ι α‖ ≤ ((C ↘ Spec (CommRingCat.of k₀)).residueCard x.1 : ℝ) ^ (β / 2) := by
  have : LocallyOfFiniteType (X' ↘ Spec (CommRingCat.of k₀)) :=
    haveI := SmoothOfRelativeDimension.smooth 1 (X' ↘ Spec (CommRingCat.of k₀))
    inferInstance
  have hjp : j ≫ C ↘ Spec (CommRingCat.of k₀) = U ↘ Spec (CommRingCat.of k₀) := comp_over j _
  have : LocallyOfFiniteType (U ↘ Spec (CommRingCat.of k₀)) := hjp ▸ inferInstance
  obtain ⟨E⟩ := nonempty_equiv_stalk_directImage_of_isPullback h F y x hyx
  have hF' : ((upperStar i').obj F).IsLisse := ProEtale.IsAdicLisseSheaf.upperStar _ hF
  have key := hasWeightsAtMost_directImage j' ι hF' (hw.upperStar_of_isOpenImmersion i') y α
    (E.hasEigenvalue hα)
  rwa [Scheme.Hom.residueCard, degreeOver_eq_of_isOpenImmersion i, hyx,
    ← Scheme.Hom.residueCard] at key

end Semicontinuity

end AlgebraicGeometry.WeilSheaf
