import Langlands.Representation.Classification.ChosenUnitaryNormalizationStatement
import Langlands.LocalField.Uniformizer

/-!
# Square-integrability at a chosen unitary normalization

The scalar action of a square-integrable normalization and the invariant form
of the chosen normalization force their exponents to agree.
-/

open scoped NNReal

namespace Langlands.Classification

universe uF uV

/-- Removing any exponent supplied with an invariant positive form gives the
full analytic square-integrability predicate. -/
theorem chosenUnitarySquareIntegrability {p : ℕ} [Fact p.Prime]
    (F : PadicField.{uF} p) (T : F.TopologicalData) :
    ChosenUnitarySquareIntegrability.{uF, uV} F T := by
  classical
  intro n hn
  let := T.topology
  have := T.generalLinearTopologicalGroup n
  let := T.centralQuotientMeasurableSpace n
  have := T.centralQuotientBorelSpace n
  intro π hπ hess d
  obtain ⟨s, hs⟩ := hess
  obtain ⟨μ, hμ⟩ := T.exists_isHaarMeasure_centralQuotient n
  have := hμ
  obtain ⟨c, _⟩ := (hs μ).2
  have := hπ
  have : Nontrivial π :=
    IsSimpleModule.nontrivial
      (MonoidAlgebra ℂ (GeneralLinear n F.Carrier)) π.representation.asModule
  obtain ⟨v, hv⟩ := exists_ne (0 : π)
  let : InnerProductSpace.Core ℂ π := d.form.toInnerProductCore
  let : Inner ℂ π := ⟨d.form.inner⟩
  have hb : d.form.inner v v ≠ 0 := fun h => hv (d.form.definite v h)
  let z : Subgroup.center (GeneralLinear n F.Carrier) :=
    GeneralLinear.scalarToCenter (LocalFactor.PadicAbelian.uniformizerUnit T)
  let x : ℝ := ((T.determinantNorm n z : ℝ≥0) : ℝ)
  have hx : 0 < x := by
    exact_mod_cast (pos_iff_ne_zero.mpr (T.determinantNorm n z).ne_zero)
  have htw :
      realPowerTwist (T.determinantNorm n) (-d.exponent) π.representation =
        realPowerTwist (T.determinantNorm n) (s - d.exponent)
          (realPowerTwist (T.determinantNorm n) (-s) π.representation) := by
    rw [← realPowerTwist_add]
    congr 1
    ring
  let k : ℂ := (x ^ (s - d.exponent) : ℝ) * (c.character z : ℂ)
  have haction :
      realPowerTwist (T.determinantNorm n) (-d.exponent) π.representation z v =
        k • v := by
    rw [htw, realPowerTwist_apply, c.acts, smul_smul]
  have hinvariant := d.form.invariant z v v
  rw [haction] at hinvariant
  change inner ℂ (k • v) (k • v) = inner ℂ v v at hinvariant
  rw [InnerProductSpace.Core.inner_smul_left,
    InnerProductSpace.Core.inner_smul_right] at hinvariant
  have hproduct : starRingEnd ℂ k * k = 1 := by
    apply mul_right_cancel₀ hb
    simpa only [mul_assoc, one_mul] using hinvariant
  have hnorm : ‖k‖ = 1 := by
    have h := congrArg norm hproduct
    change ‖star k * k‖ = ‖(1 : ℂ)‖ at h
    simp only [norm_mul, norm_star, norm_one] at h
    nlinarith [norm_nonneg k]
  have hpower : x ^ (s - d.exponent) = 1 := by
    simpa only [k, norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (Real.rpow_pos_of_pos hx _), c.norm_eq_one, mul_one] using hnorm
  have huniformizer : T.normalizedAbs T.uniformizer < 1 := by
    rw [T.normalizedAbs_uniformizer, zpow_neg_one]
    exact inv_lt_one_of_one_lt₀ (by exact_mod_cast T.residueCardinality_gt_one)
  have hxlt : x < 1 := by
    change (((T.determinantNorm n
      (GeneralLinear.scalar (LocalFactor.PadicAbelian.uniformizerUnit T)) : ℝ≥0) : ℝ)) < 1
    rw [T.determinantNorm_scalar]
    change T.normalizedAbs
      (LocalFactor.PadicAbelian.uniformizerUnit T : F.Carrier) ^ n < 1
    rw [LocalFactor.PadicAbelian.uniformizerUnit_coe]
    exact pow_lt_one₀ (T.normalizedAbs_nonneg _) huniformizer (Nat.ne_of_gt hn)
  have hdiff : s - d.exponent = 0 :=
    (Real.rpow_right_inj hx (ne_of_lt hxlt)).mp
      (by simpa only [Real.rpow_zero] using hpower)
  have hsa : s = d.exponent := sub_eq_zero.mp hdiff
  simpa only [hsa] using hs

end Langlands.Classification
