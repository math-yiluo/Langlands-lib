import Langlands.Global.AdelicEisensteinRightTranslation
import Langlands.Global.AdelicGroupProduct
import Langlands.Global.InfiniteAdelicGroupManifold
import Langlands.Geometry.Manifold.SmoothGroupDirectionalLimit
import Mathlib.Analysis.Normed.Group.FunctionSeries

/-! # Invariant differentiation of the convergent adelic Eisenstein sum -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry NumberField Filter Set
open scoped CategoryTheory.MonObj Manifold ContDiff

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 900000

namespace Langlands.Global.AdelicGroupPoints

open InfiniteAdelicGroupPoints Langlands.Geometry.Manifold

variable {F : Type u} [Field F] [NumberField F]
  {G P : GroupScheme (Spec (CommRingCat.of F))} [IsAffine G.X.left]
  {p : P ⟶ G} {K : Subgroup (AdelicGroupPoints F G)}
  (hK : IsIwasawaCompact p K) {d : ℕ} (hsmooth : SmoothOfRelativeDimension d G.X.hom)

local notation "𝓘∞" => 𝓘(ℝ, smoothModel F d)
local notation "𝓘ℂ" => 𝓘(ℝ, ℂ)

namespace IsIwasawaCompact

/-- Take the actual invariant derivative of the twisted section, then
transport back to the untwisted scalar carrier by the inverse twist. -/
def parameterDirectionalSection (lam : ComplexCharacterParameter F P)
    (X : smoothModel F d) (φ : AdelicGroupPoints F G → ℂ) : AdelicGroupPoints F G → ℂ := by
  letI := fun v : InfinitePlace F => InfinitePlaceGroupPoints.completionRCLike F v
  letI := smoothChartedSpace F G hsmooth
  exact (hK.parameterTwistEquiv lam).symm fun g =>
    groupDirectionalValue 𝓘∞ X
      (fun a => hK.parameterTwist φ lam (pair F G a (finite F G g))) (infinite F G g)

theorem parameterTwist_directionalSection (lam : ComplexCharacterParameter F P)
    (X : smoothModel F d) (φ : AdelicGroupPoints F G → ℂ)
    (a : InfiniteAdelicGroupPoints F G) (b : FiniteAdelicGroupPoints F G) :
    letI := fun v : InfinitePlace F => InfinitePlaceGroupPoints.completionRCLike F v
    letI := smoothChartedSpace F G hsmooth
    hK.parameterTwist (hK.parameterDirectionalSection hsmooth lam X φ) lam (pair F G a b) =
      groupDirectionalValue 𝓘∞ X (fun z => hK.parameterTwist φ lam (pair F G z b)) a := by
  let := fun v : InfinitePlace F => InfinitePlaceGroupPoints.completionRCLike F v
  let := smoothChartedSpace F G hsmooth
  let df (g : AdelicGroupPoints F G) :=
    groupDirectionalValue 𝓘∞ X
      (fun z => hK.parameterTwist φ lam (pair F G z (finite F G g))) (infinite F G g)
  have h := congrFun ((hK.parameterTwistEquiv lam).apply_symm_apply df) (pair F G a b)
  change hK.parameterTwist (hK.parameterDirectionalSection hsmooth lam X φ) lam
    (pair F G a b) = df (pair F G a b) at h
  simpa only [df, infinite_pair, finite_pair] using h

/-- The same derivative applies on a rational left translate of the infinite
slice, because it commutes with left translation. -/
theorem directionalValue_eisensteinTerm (lam : ComplexCharacterParameter F P)
    (X : smoothModel F d) (φ : AdelicGroupPoints F G → ℂ)
    (a : InfiniteAdelicGroupPoints F G) (b : FiniteAdelicGroupPoints F G)
    (c : ParabolicRationalCosets F p) :
    letI := fun v : InfinitePlace F => InfinitePlaceGroupPoints.completionRCLike F v
    letI := smoothChartedSpace F G hsmooth
    groupDirectionalValue 𝓘∞ X
      (fun z => hK.eisensteinTerm φ lam (pair F G z b) c) a =
      hK.eisensteinTerm (hK.parameterDirectionalSection hsmooth lam X φ) lam (pair F G a b) c := by
  let := fun v : InfinitePlace F => InfinitePlaceGroupPoints.completionRCLike F v
  let := smoothChartedSpace F G hsmooth
  let γ := ((Quotient.out c : rationalSubgroup F G) : AdelicGroupPoints F G)
  have hleft (z : InfiniteAdelicGroupPoints F G) :
      γ * pair F G z b = pair F G (infinite F G γ * z) (finite F G γ * b) := by
    rw [← pair_projections F G γ, pair_mul]
    simp only [infinite_pair, finite_pair]
  change groupDirectionalValue 𝓘∞ X
    (fun z => hK.parameterTwist φ lam (γ * pair F G z b)) a =
      hK.parameterTwist (hK.parameterDirectionalSection hsmooth lam X φ) lam (γ * pair F G a b)
  simp only [hleft]
  let slice (z : InfiniteAdelicGroupPoints F G) :=
    hK.parameterTwist φ lam (pair F G z (finite F G γ * b))
  exact (groupDirectionalValue_leftTranslation 𝓘∞ X (infinite F G γ) slice a).trans
    (hK.parameterTwist_directionalSection hsmooth lam X φ
      (infinite F G γ * a) (finite F G γ * b)).symm

private theorem tendstoLocallyUniformly_tsum_of_majorant
    {Index Y : Type*} [TopologicalSpace Y] [LocallyCompactSpace Y] (f : Index → Y → ℂ)
    (h : ∀ C : Set Y, IsCompact C →
      ∃ u : Index → ℝ, Summable u ∧ ∀ c y, y ∈ C → ‖f c y‖ ≤ u c) :
    TendstoLocallyUniformly (fun T : Finset Index => fun y => ∑ c ∈ T, f c y)
      (fun y => ∑' c, f c y) atTop := by
  apply tendstoLocallyUniformly_iff_forall_isCompact.mpr
  intro C hC
  obtain ⟨u, hu, hb⟩ := h C hC
  exact tendstoUniformlyOn_tsum hu hb

set_option backward.isDefEq.respectTransparency true in
private theorem tendsto_eisensteinSlice [LocallyOfFiniteType G.X.hom]
    (lam : ComplexCharacterParameter F P) (φ : AdelicGroupPoints F G → ℂ)
    (hφ : ∀ C : Set (AdelicGroupPoints F G), IsCompact C →
      ∃ u : ParabolicRationalCosets F p → ℝ, Summable u ∧
        ∀ c g, g ∈ C → ‖hK.eisensteinTerm φ lam g c‖ ≤ u c)
    (b : FiniteAdelicGroupPoints F G) :
    TendstoLocallyUniformly
      (fun T : Finset (ParabolicRationalCosets F p) =>
        fun a => ∑ c ∈ T, hK.eisensteinTerm φ lam (pair F G a b) c)
      (fun a => hK.eisensteinSeries φ lam (pair F G a b)) atTop := by
  let f (c : ParabolicRationalCosets F p) (a : InfiniteAdelicGroupPoints F G) :=
    hK.eisensteinTerm φ lam (pair F G a b) c
  change TendstoLocallyUniformly
    (fun T : Finset (ParabolicRationalCosets F p) => fun a => ∑ c ∈ T, f c a)
    (fun a => ∑' c, f c a) atTop
  refine @tendstoLocallyUniformly_tsum_of_majorant (ParabolicRationalCosets F p)
    (InfiniteAdelicGroupPoints F G) _ (InfiniteAdelicGroupPoints.locallyCompactSpace F G) f ?_
  intro C hC
  let embed (a : InfiniteAdelicGroupPoints F G) := pair F G a b
  have hpair : Continuous (fun a : InfiniteAdelicGroupPoints F G => (a, b)) :=
    Continuous.prodMk_left b
  have hEmbed : Continuous embed := by
    change Continuous ((fun p : InfiniteAdelicGroupPoints F G × FiniteAdelicGroupPoints F G =>
      pair F G p.1 p.2) ∘ fun a => (a, b))
    exact (continuous_pair F G).comp hpair
  obtain ⟨u, hu, hbound⟩ := hφ (embed '' C) (hC.image hEmbed)
  exact ⟨u, hu, fun c a ha => hbound c (embed a) (mem_image_of_mem embed ha)⟩

/-- Local absolute majorants for the input and its first invariant
derivatives suffice for differential covariance of the actual sum. -/
theorem directionalValue_eisensteinSeries [LocallyOfFiniteType G.X.hom]
    (lam : ComplexCharacterParameter F P) (φ : AdelicGroupPoints F G → ℂ)
    (hφ : letI := fun v : InfinitePlace F => InfinitePlaceGroupPoints.completionRCLike F v
      letI := smoothChartedSpace F G hsmooth
      ∀ b, ContMDiff 𝓘∞ 𝓘ℂ ∞ (fun a => hK.parameterTwist φ lam (pair F G a b)))
    (hE : letI := fun v : InfinitePlace F => InfinitePlaceGroupPoints.completionRCLike F v
      letI := smoothChartedSpace F G hsmooth
      ∀ b, ContMDiff 𝓘∞ 𝓘ℂ ∞ (fun a => hK.eisensteinSeries φ lam (pair F G a b)))
    (hb₀ : ∀ C : Set (AdelicGroupPoints F G), IsCompact C →
      ∃ u : ParabolicRationalCosets F p → ℝ, Summable u ∧
        ∀ c g, g ∈ C → ‖hK.eisensteinTerm φ lam g c‖ ≤ u c)
    (hb₁ : ∀ X (C : Set (AdelicGroupPoints F G)), IsCompact C →
      ∃ u : ParabolicRationalCosets F p → ℝ, Summable u ∧
        ∀ c g, g ∈ C →
          ‖hK.eisensteinTerm (hK.parameterDirectionalSection hsmooth lam X φ) lam g c‖ ≤ u c)
    (X : smoothModel F d) (a : InfiniteAdelicGroupPoints F G) (b : FiniteAdelicGroupPoints F G) :
    letI := fun v : InfinitePlace F => InfinitePlaceGroupPoints.completionRCLike F v
    letI := smoothChartedSpace F G hsmooth
    groupDirectionalValue 𝓘∞ X (fun z => hK.eisensteinSeries φ lam (pair F G z b)) a =
      hK.eisensteinSeries (hK.parameterDirectionalSection hsmooth lam X φ) lam (pair F G a b) := by
  let := fun v : InfinitePlace F => InfinitePlaceGroupPoints.completionRCLike F v
  let := smoothChartedSpace F G hsmooth
  let := smoothLieGroup F G hsmooth
  classical
  have hterm (c : ParabolicRationalCosets F p) :
      ContMDiff 𝓘∞ 𝓘ℂ ∞ (fun z => hK.eisensteinTerm φ lam (pair F G z b) c) := by
    let γ := ((Quotient.out c : rationalSubgroup F G) : AdelicGroupPoints F G)
    have hleft (z : InfiniteAdelicGroupPoints F G) :
        γ * pair F G z b = pair F G (infinite F G γ * z) (finite F G γ * b) := by
      rw [← pair_projections F G γ, pair_mul]
      simp only [infinite_pair, finite_pair]
    change ContMDiff 𝓘∞ 𝓘ℂ ∞ (fun z => hK.parameterTwist φ lam (γ * pair F G z b))
    simp only [hleft]
    exact (hφ (finite F G γ * b)).comp
      (contMDiff_const.mul contMDiff_id :
        ContMDiff 𝓘∞ 𝓘∞ ∞ (fun z : InfiniteAdelicGroupPoints F G => infinite F G γ * z))
  let partialSum (T : Finset (ParabolicRationalCosets F p)) (z : InfiniteAdelicGroupPoints F G) :=
    ∑ c ∈ T, hK.eisensteinTerm φ lam (pair F G z b) c
  have hs (T : Finset (ParabolicRationalCosets F p)) : ContMDiff 𝓘∞ 𝓘ℂ ∞ (partialSum T) :=
    ContMDiff.sum fun c _ => hterm c
  have hder (Y : smoothModel F d) (T : Finset (ParabolicRationalCosets F p)) :
      groupDirectionalValue 𝓘∞ Y (partialSum T) = fun z => ∑ c ∈ T,
        hK.eisensteinTerm (hK.parameterDirectionalSection hsmooth lam Y φ) lam (pair F G z b) c := by
    induction T using Finset.induction_on with
    | empty =>
      funext z
      simp only [partialSum, Finset.sum_empty]
      change mvfderiv 𝓘∞ (fun _ : InfiniteAdelicGroupPoints F G => (0 : ℂ)) 1 Y = 0
      exact congrArg (fun D : TangentSpace 𝓘∞ (1 : InfiniteAdelicGroupPoints F G) →L[ℝ] ℂ =>
        D Y) (mvfderiv_const (I := 𝓘∞) 0)
    | @insert c T hc ih =>
      funext z
      have heq : partialSum (insert c T) =
          (fun z => hK.eisensteinTerm φ lam (pair F G z b) c) + partialSum T := by
        funext x
        exact Finset.sum_insert hc
      calc
        _ = groupDirectionalValue 𝓘∞ Y
            ((fun z => hK.eisensteinTerm φ lam (pair F G z b) c) + partialSum T) z :=
          congrArg (fun t => groupDirectionalValue 𝓘∞ Y t z) heq
        _ = groupDirectionalValue 𝓘∞ Y (fun z => hK.eisensteinTerm φ lam (pair F G z b) c) z +
            groupDirectionalValue 𝓘∞ Y (partialSum T) z :=
          groupDirectionalValue_add 𝓘∞ Y (hterm c) (hs T) z
        _ = _ :=
          (congrArg₂ (· + ·) (hK.directionalValue_eisensteinTerm hsmooth lam Y φ z b c)
            (congrFun ih z)).trans (Finset.sum_insert hc).symm
  let D (Y : smoothModel F d) (z : InfiniteAdelicGroupPoints F G) :=
    hK.eisensteinSeries (hK.parameterDirectionalSection hsmooth lam Y φ) lam (pair F G z b)
  refine groupDirectionalValue_of_tendstoLocallyUniformly (f := partialSum) (D := D)
    hs (hE b) (hK.tendsto_eisensteinSlice lam φ hb₀ b) ?_ X a
  intro Y
  simpa only [hder] using
    hK.tendsto_eisensteinSlice lam (hK.parameterDirectionalSection hsmooth lam Y φ) (hb₁ Y) b

end IsIwasawaCompact

end Langlands.Global.AdelicGroupPoints
