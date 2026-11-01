import Langlands.Representation.RankinSelberg.UnipotentQuotient
import Langlands.Representation.RankinSelberg.HaarSymmetriesProof
import Langlands.Representation.RankinSelberg.RankOneMatrixFunctionalEquationComparisonReflectedHaar

/-!
# Integration of adjacent-rank unipotent orbit identities

These internal adapters use the actual normalized Haar measures. They transport
compactly supported continuous orbit identities to ambient integral identities.
-/

noncomputable section

namespace Langlands.RankinSelberg

open MeasureTheory MeasureTheory.Measure QuotientIntegration GeneralLinear Whittaker

universe uF

/-- The right-Weyl form of inverse transpose, as a homeomorphism of the actual
positive-rank matrix group. -/
def adjacentRankRightWeylInverseTranspose
    (F : Type uF) [CommRing F] [TopologicalSpace F] [IsTopologicalRing F] (n : ℕ) :
    Matrix.GeneralLinearGroup (Fin (n + 1)) F ≃ₜ
      Matrix.GeneralLinearGroup (Fin (n + 1)) F :=
  (inverseTransposeContinuous (n + 1) F).toHomeomorph.trans
    (Homeomorph.mulRight (weylLong (n + 1) F))

@[simp] theorem adjacentRankRightWeylInverseTranspose_apply
    (F : Type uF) [CommRing F] [TopologicalSpace F] [IsTopologicalRing F] (n : ℕ)
    (h : Matrix.GeneralLinearGroup (Fin (n + 1)) F) :
    adjacentRankRightWeylInverseTranspose F n h =
      inverseTranspose (n + 1) F h * weylLong (n + 1) F := rfl

variable (F : Type uF) [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F] (n : ℕ)
  [MeasurableSpace (Matrix.GeneralLinearGroup (Fin (n + 1)) F)]
  [BorelSpace (Matrix.GeneralLinearGroup (Fin (n + 1)) F)]
  [MeasurableSpace (upperUnipotent (n + 1) F)]
  [BorelSpace (upperUnipotent (n + 1) F)]

/-- Equality of left unipotent orbit averages implies equality of the ambient
integrals, with precisely the existing subgroup and GL Haar normalizations. -/
theorem adjacentRank_integral_eq_of_left_unipotent_averages
    (f q : Matrix.GeneralLinearGroup (Fin (n + 1)) F → ℂ)
    (hf : Continuous f) (hfc : HasCompactSupport f)
    (hq : Continuous q) (hqc : HasCompactSupport q) (c : ℂ)
    (havg : ∀ h, (∫ u : upperUnipotent (n + 1) F,
      f (u.val * h) ∂unipotentHaar F n) =
        c * ∫ u : upperUnipotent (n + 1) F, q (u.val * h) ∂unipotentHaar F n) :
    (∫ h, f h ∂generalLinearHaar F n) = c * ∫ h, q h ∂generalLinearHaar F n := by
  let : MeasurableSpace (LeftQuotient (upperUnipotent (n + 1) F)) := borel _
  let : BorelSpace (LeftQuotient (upperUnipotent (n + 1) F)) := ⟨rfl⟩
  have hcompat := unipotentQuotientHaar_isCompatible F n
  calc
    _ = ∫ x, quotientAverage (upperUnipotent (n + 1) F)
        (unipotentHaar F n) f x ∂unipotentQuotientHaar F n :=
      (hcompat.integral_formula f hf hfc).symm
    _ = ∫ x, c * quotientAverage (upperUnipotent (n + 1) F)
        (unipotentHaar F n) q x ∂unipotentQuotientHaar F n := by
      apply integral_congr_ae
      apply Filter.Eventually.of_forall
      intro x
      induction x using Quotient.inductionOn with
      | h h => exact havg h
    _ = c * ∫ x, quotientAverage (upperUnipotent (n + 1) F)
        (unipotentHaar F n) q x ∂unipotentQuotientHaar F n := integral_const_mul c _
    _ = _ := by rw [hcompat.integral_formula q hq hqc]

/-- Inversion converts a right orbit identity into the published left Weil
formula. Both inversions preserve the already normalized Haar measures. -/
theorem adjacentRank_integral_eq_of_right_unipotent_averages
    (f q : Matrix.GeneralLinearGroup (Fin (n + 1)) F → ℂ)
    (hf : Continuous f) (hfc : HasCompactSupport f)
    (hq : Continuous q) (hqc : HasCompactSupport q) (c : ℂ)
    (havg : ∀ h, (∫ u : upperUnipotent (n + 1) F,
      f (h * u.val) ∂unipotentHaar F n) =
        c * ∫ u : upperUnipotent (n + 1) F, q (h * u.val) ∂unipotentHaar F n) :
    (∫ h, f h ∂generalLinearHaar F n) = c * ∫ h, q h ∂generalLinearHaar F n := by
  let : IsInvInvariant (generalLinearHaar F n) := (generalLinearHaarSymmetries F n).1
  have hleft : ∀ h, (∫ u : upperUnipotent (n + 1) F,
      f ((u.val * h)⁻¹) ∂unipotentHaar F n) =
        c * ∫ u : upperUnipotent (n + 1) F,
          q ((u.val * h)⁻¹) ∂unipotentHaar F n := by
    intro h
    simp only [mul_inv_rev, ← Subgroup.coe_inv]
    have hfi := integral_inv_eq_self
      (fun u : upperUnipotent (n + 1) F => f (h⁻¹ * u.val)) (unipotentHaar F n)
    have hqi := integral_inv_eq_self
      (fun u : upperUnipotent (n + 1) F => q (h⁻¹ * u.val)) (unipotentHaar F n)
    exact hfi.trans ((havg h⁻¹).trans (congrArg (fun z : ℂ => c * z) hqi.symm))
  have he := adjacentRank_integral_eq_of_left_unipotent_averages F n
    (fun h => f h⁻¹) (fun h => q h⁻¹)
    (hf.comp continuous_inv) (hfc.comp_homeomorph (Homeomorph.inv _))
    (hq.comp continuous_inv) (hqc.comp_homeomorph (Homeomorph.inv _)) c hleft
  simpa only [integral_inv_eq_self] using he

omit [MeasurableSpace (upperUnipotent (n + 1) F)]
  [BorelSpace (upperUnipotent (n + 1) F)] in
/-- The right-Weyl inverse-transpose change of variable preserves the exact
integral-subgroup-normalized GL Haar measure. -/
theorem measurePreserving_rightWeylInverseTranspose :
    MeasurePreserving
      (fun h : Matrix.GeneralLinearGroup (Fin (n + 1)) F =>
        inverseTranspose (n + 1) F h * weylLong (n + 1) F)
      (generalLinearHaar F n) (generalLinearHaar F n) :=
  (measurePreserving_mul_right (generalLinearHaar F n) (weylLong (n + 1) F)).comp
    (generalLinearHaarSymmetries F n).2.1

omit [MeasurableSpace (upperUnipotent (n + 1) F)]
  [BorelSpace (upperUnipotent (n + 1) F)] in
/-- The corresponding integral substitution needs no integrability premise,
since the change of variable is a measure-preserving homeomorphism. -/
theorem integral_rightWeylInverseTranspose
    (q : Matrix.GeneralLinearGroup (Fin (n + 1)) F → ℂ) :
    (∫ h, q (inverseTranspose (n + 1) F h * weylLong (n + 1) F)
      ∂generalLinearHaar F n) = ∫ h, q h ∂generalLinearHaar F n := by
  let e := adjacentRankRightWeylInverseTranspose F n
  exact (measurePreserving_rightWeylInverseTranspose F n).integral_comp
    e.toMeasurableEquiv.measurableEmbedding q

omit [MeasurableSpace (Matrix.GeneralLinearGroup (Fin (n + 1)) F)]
  [BorelSpace (Matrix.GeneralLinearGroup (Fin (n + 1)) F)] in
/-- Reflection of the unipotent variable identifies the right orbit average
of the pulled-back function with the right orbit average at the transformed
base point. No Haar scalar appears. -/
theorem integral_rightWeylInverseTranspose_right_orbit
    (q : Matrix.GeneralLinearGroup (Fin (n + 1)) F → ℂ)
    (h : Matrix.GeneralLinearGroup (Fin (n + 1)) F) :
    (∫ u : upperUnipotent (n + 1) F,
      q (inverseTranspose (n + 1) F (h * u.val) * weylLong (n + 1) F)
        ∂unipotentHaar F n) =
      ∫ u : upperUnipotent (n + 1) F,
        q ((inverseTranspose (n + 1) F h * weylLong (n + 1) F) * u.val)
          ∂unipotentHaar F n := by
  have he := (measurePreserving_reflectedUnipotent_unipotentHaar F n).integral_comp
    (reflectedUnipotentEquiv n (K := F)).toHomeomorph.toMeasurableEquiv.measurableEmbedding
    (fun u : upperUnipotent (n + 1) F =>
      q ((inverseTranspose (n + 1) F h * weylLong (n + 1) F) * u.val))
  have hmul (u : upperUnipotent (n + 1) F) :
      (inverseTranspose (n + 1) F h * weylLong (n + 1) F) *
        (reflectedUnipotent u).val =
      inverseTranspose (n + 1) F (h * u.val) * weylLong (n + 1) F := by
    simp only [reflectedUnipotent_val, map_mul, mul_assoc]
    rw [← mul_assoc (weylLong (n + 1) F) (weylLong (n + 1) F),
      weylLong_mul_self, one_mul]
  simpa only [hmul] using he

/-- The integration adapter for the adjacent-rank scalar Fourier comparison:
right orbit averages at `h` and `iota(h) * w` give the ambient integral identity.
The functions are required to be continuous and compactly supported, but the
orbit comparison is the only equality premise. -/
theorem adjacentRank_integral_eq_of_reflected_right_averages
    (f q : Matrix.GeneralLinearGroup (Fin (n + 1)) F → ℂ)
    (hf : Continuous f) (hfc : HasCompactSupport f)
    (hq : Continuous q) (hqc : HasCompactSupport q) (c : ℂ)
    (havg : ∀ h, (∫ u : upperUnipotent (n + 1) F,
      f (h * u.val) ∂unipotentHaar F n) =
        c * ∫ u : upperUnipotent (n + 1) F,
          q ((inverseTranspose (n + 1) F h * weylLong (n + 1) F) * u.val)
            ∂unipotentHaar F n) :
    (∫ h, f h ∂generalLinearHaar F n) = c * ∫ h, q h ∂generalLinearHaar F n := by
  let e := adjacentRankRightWeylInverseTranspose F n
  have he := adjacentRank_integral_eq_of_right_unipotent_averages F n f
    (fun h => q (e h)) hf hfc (hq.comp e.continuous) (hqc.comp_homeomorph e) c
    (fun h => by
      change (∫ u : upperUnipotent (n + 1) F,
        f (h * u.val) ∂unipotentHaar F n) =
          c * ∫ u : upperUnipotent (n + 1) F,
            q (inverseTranspose (n + 1) F (h * u.val) * weylLong (n + 1) F)
              ∂unipotentHaar F n
      rw [integral_rightWeylInverseTranspose_right_orbit]
      exact havg h)
  exact he.trans (congrArg (fun z : ℂ => c * z)
    (integral_rightWeylInverseTranspose F n q))

end Langlands.RankinSelberg
