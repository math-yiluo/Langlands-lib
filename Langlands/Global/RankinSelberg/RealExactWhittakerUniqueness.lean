import Langlands.Global.RankinSelberg.RealAscendingWhittakerEvaluation
import Langlands.Global.RankinSelberg.RealExactBlockStandardEvaluation

/-! # Uniqueness of smooth real Whittaker evaluations on standard block models -/

noncomputable section

open Langlands.Archimedean Langlands.LocalFactor.Archimedean
open scoped Matrix.Norms.Operator

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Global.RankinSelbergGlobal.RealExactWhittakerUniqueness

open RealPrincipalSeries RealStandardCompactBanach RealStrictCharacterLanglandsQuotient
open RealExactBlockStandardEvaluation (realExactBlockStandardEvaluation)

private local instance (n : ℕ) (ds : List RealBlock) : NormedAddCommGroup (Carrier n ds) :=
  (closureSubmodule (n := n) ds).normedAddCommGroup

private local instance (n : ℕ) (ds : List RealBlock) : NormedSpace ℂ (Carrier n ds) :=
  (closureSubmodule (n := n) ds).normedSpace

variable {r : ℕ}

local notation "G" => Langlands.GeneralLinear (r + 1) ℝ
local notation "U" => Langlands.GeneralLinear.upperUnipotent (r + 1) ℝ
local notation "I" => matrixModel ℝ (r + 1)
local notation:max "V" ds:max => Automorphic.realStandardKFinite (r + 1) ds
local notation:max "R" ds:max => representation (n := r + 1) ds
local notation:max "D" ds:max => DerivativeSmoothVectors I (R ds)
local notation:max "act" ds:max => DerivativeSmoothVectors.representation I (R ds)
private abbrev incl (ds : List RealBlock) (f : V ds) : D ds :=
  (compactFiniteEquiv ds f).val

/-- Whittaker covariance of a continuous functional on the smooth standard block model. -/
def IsSmoothWhittakerEvaluation (ds : List RealBlock) (a : ℝˣ) (L : D ds →L[ℂ] ℂ) : Prop :=
  ∀ (u : U) (v : D ds), L (act ds u.val v) = realWhittakerCharacter a u.val * L v

set_option maxHeartbeats 900000 in
/-- Two continuous Whittaker evaluations are proportional on each rank-matched real standard
block model when the first is nonzero. -/
theorem exists_smul_of_smoothEvaluation (ds : List RealBlock) (hr : realRank ds = r + 1) (a : ℝˣ)
    (L₀ L : D ds →L[ℂ] ℂ) (hL₀ : IsSmoothWhittakerEvaluation ds a L₀)
    (hL : IsSmoothWhittakerEvaluation ds a L) (hL₀ne : L₀ ≠ 0) : ∃ c : ℂ, L = c • L₀ := by
  let es := ascendingExpand ds
  have hes : IsCharacterList es := by
    intro b hb
    obtain ⟨char, _, rfl⟩ := List.mem_map.mp hb
    exact ⟨char, rfl⟩
  obtain ⟨T, hT, hpre⟩ := smoothStandardQuotient_ascendingExpand r ds hr
  have hCov (M : D ds →L[ℂ] ℂ) (hM : IsSmoothWhittakerEvaluation ds a M) :
      IsSmoothWhittakerEvaluation es a (M.comp T) := by
    intro u v
    exact (congrArg M (hT u.val v)).trans (hM u (T v))
  obtain ⟨ℓ₀, hBound₀, hCov₀, hCoe₀⟩ := exists_boundedForm_of_characterEvaluation (r := r)
    es hes a (L₀.comp T) (hCov L₀ hL₀)
  obtain ⟨ℓ, hBound, hCov', hCoe⟩ := exists_boundedForm_of_characterEvaluation (r := r)
    es hes a (L.comp T) (hCov L hL)
  have hMatch {f : V ds} {f' : V es} (hf' : T (incl es f') = incl ds f) :
      functionalCoefficient es ℓ₀ f' 1 = L₀ (incl ds f) ∧
      functionalCoefficient es ℓ f' 1 = L (incl ds f) := by
    constructor
    · rw [hCoe₀, map_one, Module.End.one_apply, ContinuousLinearMap.comp_apply, hf']
    · rw [hCoe, map_one, Module.End.one_apply, ContinuousLinearMap.comp_apply, hf']
  have hℓ₀ne : ℓ₀ ≠ 0 := by
    intro hZero
    apply hL₀ne
    apply ContinuousLinearMap.ext
    have hDense := denseRange_compactFiniteEquiv (r := r) ds
    have h : (L₀ : D ds → ℂ) = (0 : D ds →L[ℂ] ℂ) :=
      hDense.equalizer L₀.continuous (ContinuousLinearMap.continuous _) (funext fun f => by
        obtain ⟨f', hf'⟩ := hpre f
        have hv := (hMatch hf').1
        rw [hZero] at hv
        exact hv.symm)
    exact congrFun h
  have hr' : realRank ((ascendingCharacters ds).map RealBlock.character) = r + 1 :=
    (realRank_ascendingExpand ds).trans hr
  obtain ⟨c, hc⟩ := hasSmoothWhittakerUniqueness_of_map_character (r := r)
    (ascendingCharacters ds) hr' a ℓ₀ ℓ hBound₀ hBound hCov₀ hCov' hℓ₀ne
  refine ⟨c, ContinuousLinearMap.ext ?_⟩
  have hDense := denseRange_compactFiniteEquiv (r := r) ds
  have h : (L : D ds → ℂ) = (c • L₀ : D ds →L[ℂ] ℂ) :=
    hDense.equalizer L.continuous (ContinuousLinearMap.continuous _) (funext fun f => by
      obtain ⟨f', hf'⟩ := hpre f
      change L (incl ds f) = c * L₀ (incl ds f)
      rw [← (hMatch hf').1, ← (hMatch hf').2, hc]
      rfl)
  exact congrFun h

/-- Exact compact-finite coefficient maps for one standard block list and character are
proportional to any nonzero such map. -/
theorem exists_smul_of_exactIntertwiner (ds : List RealBlock) (hr : realRank ds = r + 1) (a : ℝˣ)
    (B₀ B : V ds →ₗ[ℂ] (G → ℂ)) (hB₀ : IsRealWhittakerIntertwiner r ds a B₀)
    (hB : IsRealWhittakerIntertwiner r ds a B) (hB₀ne : B₀ ≠ 0) : ∃ c : ℂ, B = c • B₀ := by
  obtain ⟨L₀, hL₀⟩ := realExactBlockStandardEvaluation r ds hr a B₀ hB₀
  obtain ⟨L, hL⟩ := realExactBlockStandardEvaluation r ds hr a B hB
  have hL₀ne : L₀ ≠ 0 := by
    intro hZero
    apply hB₀ne
    ext f g
    rw [← hL₀.1 f g, hZero]
    rfl
  obtain ⟨c, hc⟩ := exists_smul_of_smoothEvaluation ds hr a L₀ L hL₀.2 hL.2 hL₀ne
  refine ⟨c, LinearMap.ext fun f => funext fun g => ?_⟩
  rw [← hL.1 f g, hc]
  change c * L₀ (act ds g (incl ds f)) = c * B₀ f g
  rw [hL₀.1]

/-- A nonzero exact coefficient map has range equal to the entire specified Whittaker model. -/
theorem realWhittakerModel_eq_range (ds : List RealBlock) (hr : realRank ds = r + 1) (a : ℝˣ)
    (B₀ : V ds →ₗ[ℂ] (G → ℂ)) (hB₀ : IsRealWhittakerIntertwiner r ds a B₀) (hB₀ne : B₀ ≠ 0) :
    realWhittakerModel r ds a = LinearMap.range B₀ := by
  apply le_antisymm
  · refine iSup_le fun B => iSup_le fun hB => ?_
    obtain ⟨c, rfl⟩ := exists_smul_of_exactIntertwiner ds hr a B₀ B hB₀ hB hB₀ne
    rintro _ ⟨f, rfl⟩
    exact ⟨c • f, by rw [map_smul]; rfl⟩
  · exact le_iSup_of_le B₀ (le_iSup_of_le hB₀ le_rfl)

/-- Smooth Whittaker evaluations and exact Whittaker coefficient maps have multiplicity one
on a rank-matched real standard block list. -/
def RealExactWhittakerUniquenessStatement : Prop :=
  ∀ (r : ℕ) (ds : List RealBlock), realRank ds = r + 1 → ∀ a : ℝˣ,
    (∀ L₀ L : DerivativeSmoothVectors (matrixModel ℝ (r + 1))
        (representation (n := r + 1) ds) →L[ℂ] ℂ,
      IsSmoothWhittakerEvaluation ds a L₀ → IsSmoothWhittakerEvaluation ds a L → L₀ ≠ 0 →
      ∃ c : ℂ, L = c • L₀) ∧
    ∀ B : Automorphic.realStandardKFinite (r + 1) ds →ₗ[ℂ] (Langlands.GeneralLinear (r + 1) ℝ → ℂ),
      IsRealWhittakerIntertwiner r ds a B → B ≠ 0 → realWhittakerModel r ds a = LinearMap.range B

theorem realExactWhittakerUniqueness : RealExactWhittakerUniquenessStatement :=
  fun _ ds hr a => ⟨exists_smul_of_smoothEvaluation ds hr a, realWhittakerModel_eq_range ds hr a⟩

end Langlands.Global.RankinSelbergGlobal.RealExactWhittakerUniqueness
