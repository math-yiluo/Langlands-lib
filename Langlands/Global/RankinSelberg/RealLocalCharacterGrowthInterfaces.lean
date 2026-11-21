import Langlands.Global.RankinSelberg.RealLocalGrowthInterfaces
import Langlands.Global.RankinSelberg.RealPrincipalSeriesReduction

/-! # Character-list normalized-growth statements for the real induction -/

noncomputable section

open Langlands.LocalFactor Langlands.LocalFactor.Archimedean
open scoped NNReal

set_option autoImplicit false

namespace Langlands.Global.RankinSelbergGlobal.RealJacquet

open ArchimedeanLocal RealPrincipalSeries

/-- A real block list all of whose blocks are one-dimensional characters. -/
def IsRealCharacterList (ds : List RealBlock) : Prop :=
  ∃ cs : List RealCharacterData, ds = cs.map RealBlock.character

namespace IsRealCharacterList

theorem nil : IsRealCharacterList [] := ⟨[], rfl⟩

theorem cons {d : RealBlock} {ds : List RealBlock} (c : RealCharacterData)
    (hd : d = RealBlock.character c) (hds : IsRealCharacterList ds) :
    IsRealCharacterList (d :: ds) := by
  obtain ⟨cs, rfl⟩ := hds
  exact ⟨c :: cs, by rw [hd]; rfl⟩

theorem append {ds es : List RealBlock} (hds : IsRealCharacterList ds)
    (hes : IsRealCharacterList es) : IsRealCharacterList (ds ++ es) := by
  obtain ⟨cs, rfl⟩ := hds
  obtain ⟨bs, rfl⟩ := hes
  exact ⟨cs ++ bs, (List.map_append ..).symm⟩

theorem map_dualBlock {ds : List RealBlock} (hds : IsRealCharacterList ds) :
    IsRealCharacterList (ds.map RealLocalJacquet.dualBlock) := by
  obtain ⟨cs, rfl⟩ := hds
  refine ⟨cs.map RealCharacterData.inverse, ?_⟩
  simp only [List.map_map]
  rfl

end IsRealCharacterList

/-- Expansion replaces every block by real characters. -/
theorem isRealCharacterList_expand (ds : List RealBlock) :
    IsRealCharacterList (expand ds) := by
  induction ds with
  | nil => exact ⟨[], rfl⟩
  | cons d ds ih =>
    obtain ⟨cs, hcs⟩ := ih
    cases d with
    | character d =>
      exact ⟨d :: cs, congrArg (RealBlock.character d :: ·) hcs⟩
    | induced d =>
      let k := d.weight.natAbs
      let c₁ := Archimedean.RealJacquetFrobenius.charData
        (RealGammaReflection.positionParity k)
        (d.exponent + (k : ℂ) / 2)
      let c₂ := Archimedean.RealJacquetFrobenius.charData 0 (d.exponent - (k : ℂ) / 2)
      exact ⟨c₁ :: c₂ :: cs,
        congrArg (RealBlock.character c₁ :: RealBlock.character c₂ :: ·) hcs⟩

private theorem clear_primal_denominator {d : ℂ} (hd : d ≠ 0) (e dd sign m md : ℂ) :
    d⁻¹ * md = sign * e * dd⁻¹ * m ↔ md = sign * (e * d / dd) * m := by
  rw [inv_mul_eq_iff_eq_mul₀ hd, div_eq_mul_inv]
  have h : d * (sign * e * dd⁻¹ * m) = sign * (e * d * dd⁻¹) * m := by ac_rfl
  rw [h]

/-- The expanded factors in a continuation package can be replaced by the original block
factors. The two integral functions and the scalar sign are fixed. -/
theorem continuationPackage_of_expand {Z Zd : ℂ → ℂ} {sign : ℂ}
    (ds es : List RealBlock) (b : ℝˣ) (c : NNReal) (hc : 0 < c)
    (hC : ContinuationPackage Z Zd
      (fun s => ((realPairLFactor (expand ds) (expand es)).denominator s)⁻¹)
      (fun s => ((realPairLFactor ((expand ds).map RealLocalJacquet.dualBlock)
        ((expand es).map RealLocalJacquet.dualBlock)).denominator s)⁻¹)
      (fun s => (realPairEpsilon (expand ds) (expand es) b c hc s : ℂ)) sign) :
    ContinuationPackage Z Zd
      (fun s => ((realPairLFactor ds es).denominator s)⁻¹)
      (fun s => ((realPairLFactor (ds.map RealLocalJacquet.dualBlock)
        (es.map RealLocalJacquet.dualBlock)).denominator s)⁻¹)
      (fun s => (realPairEpsilon ds es b c hc s : ℂ)) sign := by
  obtain ⟨σ, M, Md, hM, hMd, hZM, hZdMd, hFE⟩ := hC
  refine ⟨σ, M, Md, hM, hMd, hZM, hZdMd, ?_⟩
  have hNonzero (F : ReciprocalEntire) : ∀ᶠ s in Filter.codiscrete ℂ, F.denominator s ≠ 0 :=
    eventually_codiscrete_iff_forall_eventually_nhdsNE.mpr F.denominator_eventually_ne_zero
  filter_upwards [hFE, pairMultiplier_expand ds es b c hc,
    hNonzero (realPairLFactor (expand ds) (expand es)), hNonzero (realPairLFactor ds es)] with
    s hs hGamma hExpanded hOriginal
  have hCleared : Md (1 - s) = sign * pairMultiplier (expand ds) (expand es) b c hc s * M s :=
    (clear_primal_denominator hExpanded _ _ _ _ _).mp hs
  rw [hGamma] at hCleared
  exact (clear_primal_denominator hOriginal _ _ _ _ _).mpr hCleared

/-- `RealLocalEqualGrowthAtRank`, restricted to two character lists. -/
def RealLocalEqualCharacterGrowthAtRank (r : ℕ) : Prop :=
  ∀ (ds es : List RealBlock), IsRealCharacterList ds → IsRealCharacterList es →
  realRank ds = r + 1 → realRank es = r + 1 →
  ∀ (a : ℝˣ) (D : RealQuotientMeasureData r) (W W' : Langlands.GeneralLinear (r + 1) ℝ → ℂ)
    (Φ : SchwartzMap (Fin (r + 1) → ℝ) ℂ),
    W ∈ realUniformWhittakerModel r ds a → W' ∈ realUniformWhittakerModel r es (-a) →
    HasRealPairNormalizedGrowth ds es (ds.map RealLocalJacquet.dualBlock)
      (es.map RealLocalJacquet.dualBlock) (-a) (NNReal.sqrt ‖(a : ℝ)‖₊)
      (NNReal.sqrt_pos.mpr (nnnorm_pos.mpr a.ne_zero))
      ((RealJacquet.determinant ds (-1) : ℂ) ^ r)
      (realEqualIntegral D W W' Φ) (realEqualDualIntegral (-a) D W W' Φ)

/-- `RealLocalUnequalGrowthAtRanks`, restricted to two character lists. -/
def RealLocalUnequalCharacterGrowthAtRanks (r t : ℕ) (h : t < r) : Prop :=
  ∀ (ds es : List RealBlock), IsRealCharacterList ds → IsRealCharacterList es →
  realRank ds = r + 1 → realRank es = t + 1 →
  ∀ (a : ℝˣ) (D : RealQuotientMeasureData t) (W : Langlands.GeneralLinear (r + 1) ℝ → ℂ)
    (W' : Langlands.GeneralLinear (t + 1) ℝ → ℂ),
    W ∈ realUniformWhittakerModel r ds a → W' ∈ realUniformWhittakerModel t es (-a) →
    HasRealPairNormalizedGrowth ds es (ds.map RealLocalJacquet.dualBlock)
      (es.map RealLocalJacquet.dualBlock) (-a) (NNReal.sqrt ‖(a : ℝ)‖₊)
      (NNReal.sqrt_pos.mpr (nnnorm_pos.mpr a.ne_zero))
      ((RealJacquet.determinant ds (-1) : ℂ) ^ (t + 1) * (RealJacquet.determinant es (-1) : ℂ))
      (realUnequalIntegral h D W W') (realUnequalDualIntegral h a D W W')

/-- Adjacent-rank character-list growth: the unequal statement at ranks `r + 1` and `r`. -/
def RealLocalAdjacentCharacterGrowthAtRank (r : ℕ) : Prop :=
  RealLocalUnequalCharacterGrowthAtRanks (r + 1) r (Nat.lt_succ_self r)

/-- The block-list equal statement specializes to character lists. -/
theorem RealLocalEqualGrowthAtRank.toCharacter {r : ℕ} (hG : RealLocalEqualGrowthAtRank r) :
    RealLocalEqualCharacterGrowthAtRank r :=
  fun ds es _ _ => hG ds es

/-- The block-list unequal statement specializes to character lists. -/
theorem RealLocalUnequalGrowthAtRanks.toCharacter {r t : ℕ} {h : t < r}
    (hG : RealLocalUnequalGrowthAtRanks r t h) : RealLocalUnequalCharacterGrowthAtRanks r t h :=
  fun ds es _ _ => hG ds es

/-- The block-list adjacent statement specializes to character lists. -/
theorem RealLocalAdjacentGrowthAtRank.toCharacter {r : ℕ}
    (hG : RealLocalAdjacentGrowthAtRank r) : RealLocalAdjacentCharacterGrowthAtRank r :=
  RealLocalUnequalGrowthAtRanks.toCharacter hG

/-- Rank zero of the equal-rank character statement. -/
theorem realLocalEqualCharacterGrowthAtRank_zero : RealLocalEqualCharacterGrowthAtRank 0 :=
  realLocalEqualGrowthAtRank_zero.toCharacter

/-- Unequal character-list growth at all pairs of ranks, together with the uniform
principal-series inclusion, gives the exact unequal continuation target. -/
theorem realLocalUniformUnequalContinuation_of_characterGrowth
    (hI : RealUniformPrincipalSeriesInclusionStatement)
    (hG : ∀ (r t : ℕ) (h : t < r), RealLocalUnequalCharacterGrowthAtRanks r t h) :
    RealLocalUniformUnequalContinuationStatement := by
  intro r t h ds es hds hes a D W W' hW hW'
  have hN := hG r t h (expand ds) (expand es) (isRealCharacterList_expand ds)
    (isRealCharacterList_expand es) (by rw [realRank_expand]; exact hds)
    (by rw [realRank_expand]; exact hes) a D W W' (hI r ds hds a hW) (hI t es hes (-a) hW')
  have hU := hN.unequalContinuation
  rw [determinant_expand, determinant_expand] at hU
  exact continuationPackage_of_expand ds es (-a) _ _ hU

/-- Equal character-list growth at all positive ranks, together with the uniform
principal-series inclusion, gives the exact positive equal continuation target. -/
theorem realLocalUniformPositiveEqualContinuation_of_characterGrowth
    (hI : RealUniformPrincipalSeriesInclusionStatement)
    (hG : ∀ r : ℕ, 0 < r → RealLocalEqualCharacterGrowthAtRank r) :
    RealLocalUniformPositiveEqualContinuationStatement := by
  intro r hr ds es hds hes a D W W' Φ hW hW'
  have hN := hG r hr (expand ds) (expand es) (isRealCharacterList_expand ds)
    (isRealCharacterList_expand es) (by rw [realRank_expand]; exact hds)
    (by rw [realRank_expand]; exact hes) a D W W' Φ (hI r ds hds a hW) (hI r es hes (-a) hW')
  have hE := hN.equalContinuation
  rw [determinant_expand] at hE
  exact continuationPackage_of_expand ds es (-a) _ _ hE

end Langlands.Global.RankinSelbergGlobal.RealJacquet
