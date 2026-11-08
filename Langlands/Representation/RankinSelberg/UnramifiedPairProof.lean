import Langlands.Representation.RankinSelberg.UnramifiedPairTorusCoefficient
import Langlands.Representation.RankinSelberg.SchurCauchyEvaluation
import Langlands.Representation.RankinSelberg.UnramifiedSphericalVectorProof
import Langlands.Representation.RankinSelberg.UnramifiedUnitaryPoleFreeProof

/-!
# The unramified computation of Rankin–Selberg integrals
-/

noncomputable section

open MeasureTheory

namespace Langlands.RankinSelberg

open GeneralLinear GeneralLinear.Spherical Whittaker Conductor Correspondence

universe uF uV uW

/-- In the half-plane `Re s > -log r / log q`, the parameter `q^(-s)` has norm below `r`. -/
theorem norm_natCast_cpow_neg_lt {q : ℕ} (hq : 1 < q) {r : ℝ} (hr : 0 < r) {s : ℂ}
    (hs : -Real.log r / Real.log q < s.re) : ‖(q : ℂ) ^ (-s)‖ < r := by
  have hq0 : (0 : ℝ) < q := by exact_mod_cast lt_trans Nat.zero_lt_one hq
  have hlog : 0 < Real.log q := Real.log_pos (by exact_mod_cast hq)
  rw [Complex.norm_natCast_cpow_of_pos (lt_trans Nat.zero_lt_one hq), Complex.neg_re,
    Real.rpow_def_of_pos hq0]
  rw [div_lt_iff₀ hlog] at hs
  calc Real.exp (Real.log q * -s.re) < Real.exp (Real.log r) :=
        Real.exp_lt_exp.mpr (by linarith)
    _ = r := Real.exp_log hr

/-- Jacquet–Shalika, Euler products II, §1.4 (3): the unequal-rank integral of the
normalized spherical vectors converges for `Re s` large and equals
`det(1 - A ⊗ A' q^(-s))⁻¹`. -/
theorem unramifiedPairIntegral : UnramifiedPairIntegralStatement.{uF, uV, uW} := by
  intro p _ F n k V _ _ W _ _ π σ χ χ' q ψ abv ϖ μ hπ hσ hJ ℓ ℓ' hℓ hℓ' w w'
  let := F.canonicalTopologicalData.topology
  let := F.canonicalTopologicalData.valuativeRel
  let := F.canonicalTopologicalData.localField
  let := borel (Langlands.GeneralLinear (n + 1) F.Carrier)
  have : BorelSpace (Langlands.GeneralLinear (n + 1) F.Carrier) := ⟨rfl⟩
  let := borel (upperUnipotent (n + 1) F.Carrier)
  have : BorelSpace (upperUnipotent (n + 1) F.Carrier) := ⟨rfl⟩
  let := borel (LeftUnipotentQuotient n F.Carrier)
  let := borel (LeftUnipotentQuotient 0 F.Carrier)
  have hq : q = F.canonicalTopologicalData.residueCardinality := hJ.residueCardinality
  have hq1 : 1 < q := hq ▸ F.canonicalTopologicalData.residueCardinality_gt_one
  obtain ⟨r, hr, hcauchy⟩ :=
    exists_schurCauchy_radius (unramifiedClass F χ) (unramifiedClass F χ')
  refine ⟨-Real.log r / Real.log q, fun s hs => ?_⟩
  obtain ⟨hsum, hval⟩ := hcauchy _ (norm_natCast_cpow_neg_lt hq1 hr hs)
  obtain ⟨hconv, hint⟩ := UnramifiedPairTorus.pairIntegral_eq_tsum p F n k π σ χ χ' q ψ abv ϖ
    μ hπ hσ hJ ℓ ℓ' hℓ hℓ' w w' s hsum
  refine ⟨hconv, ?_⟩
  rw [hint, hval, unramifiedEulerFactor, Finset.prod_comm]

/-- The unramified computation of Jacquet–Shalika, Euler products II, §1.3–§1.5. -/
theorem unramifiedPair : UnramifiedPairStatement.{uF, uV, uW} :=
  ⟨unramifiedSphericalVector, unramifiedPairIntegral, unramifiedUnitaryPoleFree⟩

end Langlands.RankinSelberg
