import Langlands.Global.RankinSelberg.RealPrincipalSeriesQuotient

/-! # Ascending Whittaker descent from proportionality and nonvanishing -/

noncomputable section

open Langlands.Archimedean Langlands.LocalFactor.Archimedean
open scoped Matrix.Norms.Operator

set_option autoImplicit false

namespace Langlands.Global.RankinSelbergGlobal.RealPrincipalSeries

local notation "Coeff[" r "," ds "]" =>
  Automorphic.realStandardKFinite (r + 1) ds →ₗ[ℂ] (Langlands.GeneralLinear (r + 1) ℝ → ℂ)

/-- All exact real Whittaker coefficient maps of a fixed presentation are proportional
to a given nonzero one. -/
def HasProportionalWhittakerIntertwiners (r : ℕ) (ds : List RealBlock) (a : ℝˣ) : Prop :=
  ∀ (B C : Coeff[r, ds]), IsRealWhittakerIntertwiner r ds a B →
    IsRealWhittakerIntertwiner r ds a C → C ≠ 0 → ∃ c : ℂ, B = c • C

private theorem exists_nonzeroIntertwiner {r : ℕ} {ds : List RealBlock} {a : ℝˣ}
    (h : realWhittakerModel r ds a ≠ ⊥) :
    ∃ B : Coeff[r, ds], IsRealWhittakerIntertwiner r ds a B ∧ B ≠ 0 := by
  by_contra! hZero
  apply h
  refine le_antisymm (iSup_le fun B => iSup_le fun hB => ?_) bot_le
  rw [hZero B hB, LinearMap.range_zero]

/-- The ascending source coefficients all descend if its exact intertwiners are proportional
and the original block model contains a nonzero coefficient. -/
def RealAscendingWhittakerDescentFromMultiplicityStatement : Prop :=
  ∀ (r : ℕ) (ds : List RealBlock), realRank ds = r + 1 → ∀ a : ℝˣ,
    HasProportionalWhittakerIntertwiners r (ascendingExpand ds) a →
    realWhittakerModel r ds a ≠ ⊥ →
    realWhittakerModel r (ascendingExpand ds) a ≤ realWhittakerModel r ds a

theorem realAscendingWhittakerDescentFromMultiplicity :
    RealAscendingWhittakerDescentFromMultiplicityStatement := by
  intro r ds hr a hMult hNonzero
  obtain ⟨T, hTs, hT⟩ := surjectiveIntertwiner_ascendingExpand (r + 1) ds hr
  obtain ⟨C, hC, hC₀⟩ := exists_nonzeroIntertwiner hNonzero
  have hCT := isRealWhittakerIntertwiner_pullback hT hC
  have hCT₀ : C.comp T ≠ 0 := by
    intro hz
    apply hC₀
    apply LinearMap.ext
    intro f
    obtain ⟨v, rfl⟩ := hTs f
    exact congrArg (fun L : Coeff[r, ascendingExpand ds] => L v) hz
  refine iSup_le fun B => iSup_le fun hB => ?_
  obtain ⟨c, hc⟩ := hMult B (C.comp T) hB hCT hCT₀
  rintro W ⟨f, rfl⟩
  refine Submodule.mem_iSup_of_mem C (Submodule.mem_iSup_of_mem hC ⟨c • T f, ?_⟩)
  rw [hc, map_smul]
  rfl

end Langlands.Global.RankinSelbergGlobal.RealPrincipalSeries
