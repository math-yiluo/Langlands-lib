import Langlands.Global.RankinSelberg.RealExactStandardEvaluation
import Langlands.Global.RankinSelberg.RealPrincipalSeriesQuotient

/-! # Continuous Whittaker evaluation of real standard block models -/

noncomputable section

open Langlands.Archimedean Langlands.LocalFactor.Archimedean
open scoped Matrix.Norms.Operator

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Global.RankinSelbergGlobal.RealExactBlockStandardEvaluation

open DerivativeSmoothVectors RealPrincipalSeries RealStandardCompactBanach
open RealCompactDifferences (CompactDifferenceBound)
open RealExactStandardEvaluation (exists_continuous_identityEvaluation
  isWhittakerStandardEvaluation_of_identity)
open RealWhittakerFiniteOrder (realWhittakerFiniteOrder)

private local instance (n : ℕ) (ds : List RealBlock) : NormedAddCommGroup (Carrier n ds) :=
  (closureSubmodule (n := n) ds).normedAddCommGroup

private local instance (n : ℕ) (ds : List RealBlock) : NormedSpace ℂ (Carrier n ds) :=
  (closureSubmodule (n := n) ds).normedSpace

variable {r : ℕ}

local notation "G" => Langlands.GeneralLinear (r + 1) ℝ
local notation:max "V" ds:max => Automorphic.realStandardKFinite (r + 1) ds

/-- The finite compact difference bound for character series descends to each standard block
list of the given rank. -/
theorem exists_blockFiniteOrder (ds : List RealBlock) (hr : realRank ds = r + 1) (a : ℝˣ)
    (B : V ds →ₗ[ℂ] (G → ℂ)) (hB : IsRealWhittakerIntertwiner r ds a B) :
    ∃ (J : ℕ) (C : ℝ), 0 ≤ C ∧ ∀ (f : V ds) (R : ℝ),
      CompactDifferenceBound J f R → ‖B f 1‖ ≤ C * R := by
  obtain ⟨T, S, hT, hTS, hS, A, hA, hBound⟩ := compactlySplitStandardQuotient_ascendingExpand _ ds hr
  obtain ⟨J, C, hC, hOrder⟩ := realWhittakerFiniteOrder r (ascendingCharacters ds) a (B.comp T)
    (isRealWhittakerIntertwiner_pullback hT hB)
  refine ⟨J, C * A, mul_nonneg hC hA, fun f R hf => ?_⟩
  have hLift := compactDifferenceBound_of_compactBound S hS hBound hf
  have he : T (S f) = f := hTS f
  have h := hOrder (S f) (A * R) hLift
  change ‖B (T (S f)) 1‖ ≤ C * (A * R) at h
  rw [he] at h
  simpa only [mul_assoc] using h

/-- Every exact real Whittaker map of a rank-matched standard module is realized by a
continuous Whittaker functional on its genuine smooth vectors. -/
def RealExactBlockStandardEvaluationStatement : Prop :=
  ∀ (r : ℕ) (ds : List RealBlock), realRank ds = r + 1 →
    ∀ (a : ℝˣ) (B : Automorphic.realStandardKFinite (r + 1) ds →ₗ[ℂ]
      (Langlands.GeneralLinear (r + 1) ℝ → ℂ)), IsRealWhittakerIntertwiner r ds a B →
      ∃ L : DerivativeSmoothVectors (matrixModel ℝ (r + 1))
          (representation (n := r + 1) ds) →L[ℂ] ℂ, IsWhittakerStandardEvaluation ds a B L

theorem realExactBlockStandardEvaluation : RealExactBlockStandardEvaluationStatement := by
  intro r ds hr a B hB
  obtain ⟨J, C, hC, hOrder⟩ := exists_blockFiniteOrder ds hr a B hB
  obtain ⟨L, hL⟩ := exists_continuous_identityEvaluation ds B J C hC hOrder
  exact ⟨L, isWhittakerStandardEvaluation_of_identity ds a B hB L hL⟩

end Langlands.Global.RankinSelbergGlobal.RealExactBlockStandardEvaluation
