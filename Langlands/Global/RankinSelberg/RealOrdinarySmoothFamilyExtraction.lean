import Langlands.Global.RankinSelberg.RealOrdinaryTestExtraction
import Langlands.Global.RankinSelberg.RealSmoothNormalizedEvaluationContinuity

/-! # Compact-finite extraction from entire smooth real ordinary families -/

noncomputable section

open Set
open scoped Matrix.Norms.Operator SchwartzMap

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 650000

namespace Langlands.Global.RankinSelbergGlobal.RealOrdinarySmoothFamilyExtraction

open Langlands.Archimedean Langlands.LocalFactor Langlands.LocalFactor.Archimedean
open RealStandardCompactBanach RealOrdinaryTestExtraction
open RealSmoothNormalizedEvaluationContinuity (realSmoothNormalizedEvaluationContinuity)
open ArchimedeanLocal

private local instance (n : ℕ) (ds : List RealBlock) : NormedAddCommGroup (Carrier n ds) :=
  (closureSubmodule (n := n) ds).normedAddCommGroup

private local instance (n : ℕ) (ds : List RealBlock) : NormedSpace ℂ (Carrier n ds) :=
  (closureSubmodule (n := n) ds).normedSpace

local notation "G[" r "]" => Langlands.GeneralLinear (r + 1) ℝ
local notation "Std[" r "," d "]" => Automorphic.realStandardKFinite (r + 1) d
local notation "Smooth[" r "," d "]" => DerivativeSmoothVectors (matrixModel ℝ (r + 1))
  (RealStandardCompactBanach.representation (n := r + 1) d)

variable {r t : ℕ} {d e : List RealBlock}

/-- An entire bilinear family on two smooth standard modules whose spectral evaluations
are separately continuous on a nonempty open set of spectral parameters. -/
def HasSmoothPairInitialContinuity (F : Smooth[r,d] →ₗ[ℂ] Smooth[t,e] →ₗ[ℂ] (ℂ → ℂ)) : Prop :=
  (∀ v w, Differentiable ℂ (F v w)) ∧
    ∃ U : Set ℂ, IsOpen U ∧ U.Nonempty ∧ ∀ z ∈ U,
      (∀ w, Continuous (fun v => F v w z)) ∧ (∀ v, Continuous (fun w => F v w z))

private theorem exists_compact_pair_ne_zero (F : Smooth[r,d] →ₗ[ℂ] Smooth[t,e] →ₗ[ℂ] (ℂ → ℂ))
    (hF : HasSmoothPairInitialContinuity F) (s : ℂ) (h : ∃ v w, F v w s ≠ 0) :
    ∃ (v : Std[r,d]) (w : Std[t,e]), F (smoothOfCompact d v) (smoothOfCompact e w) s ≠ 0 := by
  obtain ⟨hent, U, hU, hUn, hEval⟩ := hF
  have hv (w : Smooth[t,e]) : Continuous (fun v => F v w s) :=
    realSmoothNormalizedEvaluationContinuity (r + 1) d ((LinearMap.applyₗ w).comp F)
      (fun v => hent v w) U hU hUn (fun z hz => (hEval z hz).1 w) s
  have hw (v : Smooth[r,d]) : Continuous (fun w => F v w s) :=
    realSmoothNormalizedEvaluationContinuity (t + 1) e (F v)
      (hent v) U hU hUn (fun z hz => (hEval z hz).2 v) s
  by_contra! hz
  have he (w : Std[t,e]) : (fun v => F v (smoothOfCompact e w) s) = fun _ => 0 :=
    (denseRange_compactFiniteEquiv d).equalizer (hv (smoothOfCompact e w)) continuous_const
      (funext fun v => hz v w)
  have hd (v : Smooth[r,d]) : (fun w => F v w s) = fun _ => 0 :=
    (denseRange_compactFiniteEquiv e).equalizer (hw v) continuous_const
      (funext fun w => congrFun (he w) v)
  obtain ⟨v, w, hne⟩ := h
  exact hne (congrFun (hd v) w)

/-- Coverage of unequal-rank ordinary normalized values follows from a separately
continuous initial smooth family with an entire extension and pointwise coverage. -/
def RealUnequalSmoothFamilyExtractionStatement : Prop :=
  ∀ (r t : ℕ) (h : t < r) (d e : List RealBlock) (a : ℝˣ) (D : RealQuotientMeasureData t)
    (B : Std[r,d] →ₗ[ℂ] (G[r] → ℂ)) (C : Std[t,e] →ₗ[ℂ] (G[t] → ℂ))
    (hB : IsRealWhittakerIntertwiner r d a B) (hC : IsRealWhittakerIntertwiner t e (-a) C)
    (F : Smooth[r,d] →ₗ[ℂ] Smooth[t,e] →ₗ[ℂ] (ℂ → ℂ)),
    HasSmoothPairInitialContinuity F → (∀ s, ∃ v w, F v w s ≠ 0) →
    (∀ (v : Std[r,d]) (w : Std[t,e]),
      ∃ N : OrdinaryIntegralNormalization
        (realOrdinaryUnequalTest h d e a D (coefficient B hB v, coefficient C hC w))
        (fun s => ((realPairLFactor d e).denominator s)⁻¹),
        N.value = F (smoothOfCompact d v) (smoothOfCompact e w)) →
    HasCoveringOrdinaryNormalizations (realOrdinaryUnequalTest h d e a D) (realPairLFactor d e)

theorem realUnequalSmoothFamilyExtraction : RealUnequalSmoothFamilyExtractionStatement := by
  intro r t h d e a D B C hB hC F hF hCover hTrace s
  obtain ⟨v, w, hz⟩ := exists_compact_pair_ne_zero F hF s (hCover s)
  obtain ⟨N, hN⟩ := hTrace v w
  exact ⟨(coefficient B hB v, coefficient C hC w), N, fun hn => hz (congrFun hN s ▸ hn)⟩

/-- For equal ranks, the same density argument applies with a fixed Schwartz row at
any selected spectral point. -/
def RealEqualSmoothFamilyExtractionStatement : Prop :=
  ∀ (r : ℕ) (d e : List RealBlock) (a : ℝˣ) (D : RealQuotientMeasureData r)
    (B : Std[r,d] →ₗ[ℂ] (G[r] → ℂ)) (C : Std[r,e] →ₗ[ℂ] (G[r] → ℂ))
    (hB : IsRealWhittakerIntertwiner r d a B) (hC : IsRealWhittakerIntertwiner r e (-a) C)
    (F : 𝓢((Fin (r + 1) → ℝ), ℂ) → Smooth[r,d] →ₗ[ℂ] Smooth[r,e] →ₗ[ℂ] (ℂ → ℂ)),
    (∀ Φ, HasSmoothPairInitialContinuity (F Φ)) → (∀ s, ∃ Φ v w, F Φ v w s ≠ 0) →
    (∀ (v : Std[r,d]) (w : Std[r,e]) (Φ : 𝓢((Fin (r + 1) → ℝ), ℂ)),
      ∃ N : OrdinaryIntegralNormalization
        (realOrdinaryEqualTest r d e a D (coefficient B hB v, coefficient C hC w, Φ))
        (fun s => ((realPairLFactor d e).denominator s)⁻¹),
        N.value = F Φ (smoothOfCompact d v) (smoothOfCompact e w)) →
    HasCoveringOrdinaryNormalizations (realOrdinaryEqualTest r d e a D) (realPairLFactor d e)

theorem realEqualSmoothFamilyExtraction : RealEqualSmoothFamilyExtractionStatement := by
  intro r d e a D B C hB hC F hF hCover hTrace s
  obtain ⟨Φ, hΦ⟩ := hCover s
  obtain ⟨v, w, hz⟩ := exists_compact_pair_ne_zero (F Φ) (hF Φ) s hΦ
  obtain ⟨N, hN⟩ := hTrace v w Φ
  exact ⟨(coefficient B hB v, coefficient C hC w, Φ), N, fun hn => hz (congrFun hN s ▸ hn)⟩

/-- Compact-finite test extraction from separately continuous initial data in both
real ordinary integral families. -/
def RealOrdinarySmoothFamilyExtractionStatement : Prop :=
  RealUnequalSmoothFamilyExtractionStatement ∧ RealEqualSmoothFamilyExtractionStatement

theorem realOrdinarySmoothFamilyExtraction : RealOrdinarySmoothFamilyExtractionStatement :=
  ⟨realUnequalSmoothFamilyExtraction, realEqualSmoothFamilyExtraction⟩

end Langlands.Global.RankinSelbergGlobal.RealOrdinarySmoothFamilyExtraction
