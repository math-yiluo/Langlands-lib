import Langlands.Global.Factors.GLPoleRegionTransport
import Langlands.Representation.RankinSelberg.AnalyticTemperedTwistLPolynomialData
import Langlands.Representation.RankinSelberg.CenteredBlockLPolynomialProof
import Langlands.Representation.Classification.InverseTransposeAnalyticProof
import Langlands.Representation.CuspidalSupport.CuspidalTensorAssociationProof
import Langlands.Representation.Twist.SubquotientProof

/-!
# The essentially tempered case of the GL pole-region statement

For irreducible essentially tempered `π` and `σ` over the canonical realization of
a p-adic field, the p-adic pair L-polynomial `P` of `(π, σ)` for `ψ` and the
p-adic pair L-polynomial `Pdual` of `(π^ι, σ^ι)` for `ψ⁻¹` have no reflected
common zero.
-/

noncomputable section

namespace Langlands.Global.GLPoleRegion

universe uF uV uW

open HarmonicAnalysis Whittaker GeneralLinear RankinSelberg Polynomial

variable {p : ℕ} [Fact p.Prime] {F : PadicField.{uF} p}

/-- Essentially tempered case: if `π = π₀ ⊗ |det|^a` and `σ = σ₀ ⊗ |det|^b` with
`π₀`, `σ₀` irreducible tempered, then `P` has no zero in `‖z‖ < q^(a+b)`, the dual
polynomial has no zero in `‖w‖ < q^(-a-b)`, and hence there is no reflected common
zero. -/
theorem hasNoReflectedCommonZero_of_essentiallyTempered
    {ψ : letI := F.canonicalTopologicalData.topology; UnitaryAdditiveCharacter F.Carrier}
    (ν : LocalFactor.PadicAbelian.SelfDualHaar F.canonicalTopologicalData ψ)
    (νd : letI := F.canonicalTopologicalData.topology
      letI := F.canonicalTopologicalData.valuativeRel
      letI := F.canonicalTopologicalData.localField
      LocalFactor.PadicAbelian.SelfDualHaar F.canonicalTopologicalData (ψ.scale (-1)))
    {r t : ℕ} (htr : t ≤ r) {V : Type uV} {W : Type uW} [AddCommGroup V] [Module ℂ V]
    [AddCommGroup W] [Module ℂ W]
    {π : Representation ℂ (Langlands.GeneralLinear (r + 1) F.Carrier) V}
    {σ : Representation ℂ (Langlands.GeneralLinear (t + 1) F.Carrier) W}
    (hiπ : Representation.IsIrreducible π) (hiσ : Representation.IsIrreducible σ)
    (heπ : F.canonicalTopologicalData.IsEssentiallyTempered π)
    (heσ : F.canonicalTopologicalData.IsEssentiallyTempered σ)
    {P Pdual : ℂ[X]}
    (hP : IsPadicPairLPolynomial F ψ ν.val π σ P)
    (hPd : letI := F.canonicalTopologicalData.topology
      letI := F.canonicalTopologicalData.valuativeRel
      letI := F.canonicalTopologicalData.localField
      IsPadicPairLPolynomial F (ψ.scale (-1)) νd.val (inverseTransposePullback π)
        (inverseTransposePullback σ) Pdual) :
    HasNoReflectedCommonZero F.canonicalTopologicalData.residueCardinality P Pdual := by
  let := F.canonicalTopologicalData.topology
  let := F.canonicalTopologicalData.valuativeRel
  let := F.canonicalTopologicalData.localField
  obtain ⟨a, ha⟩ := heπ
  obtain ⟨b, hb⟩ := heσ
  obtain ⟨π₀, rfl⟩ : ∃ π₀ : Representation ℂ (Langlands.GeneralLinear (r + 1) F.Carrier) V,
      π = realPowerTwist (F.canonicalTopologicalData.determinantNorm (r + 1)) a π₀ :=
    ⟨_, (realPowerTwist_cancel_neg _ a π).symm⟩
  obtain ⟨σ₀, rfl⟩ : ∃ σ₀ : Representation ℂ (Langlands.GeneralLinear (t + 1) F.Carrier) W,
      σ = realPowerTwist (F.canonicalTopologicalData.determinantNorm (t + 1)) b σ₀ :=
    ⟨_, (realPowerTwist_cancel_neg _ b σ).symm⟩
  rw [realPowerTwist_neg_cancel] at ha hb
  have hiπ₀ : Representation.IsIrreducible π₀ := (isIrreducible_twist_iff _ π₀).1 hiπ
  have hiσ₀ : Representation.IsIrreducible σ₀ := (isIrreducible_twist_iff _ σ₀).1 hiσ
  have hP' : IsPadicSymmetricLPolynomial F ψ ν.val
      (realPowerTwist (F.canonicalTopologicalData.determinantNorm (r + 1)) a π₀)
      (realPowerTwist (F.canonicalTopologicalData.determinantNorm (t + 1)) b σ₀) P := by
    exact (isPadicSymmetricLPolynomial_of_le htr).2 hP
  have hfree := analyticTemperedTwistLPolynomial_poleFree F ψ ν π₀ σ₀ hiπ₀ ha hiσ₀ hb a b hP'
  have hiπ₀d : Representation.IsIrreducible (inverseTransposePullback π₀) :=
    CuspidalSupport.isIrreducible_comp_of_surjective π₀ (hρ := hiπ₀)
      (GeneralLinear.inverseTranspose (r + 1) F.Carrier).toMonoidHom
      (GeneralLinear.inverseTranspose (r + 1) F.Carrier).surjective
  have hiσ₀d : Representation.IsIrreducible (inverseTransposePullback σ₀) :=
    CuspidalSupport.isIrreducible_comp_of_surjective σ₀ (hρ := hiσ₀)
      (GeneralLinear.inverseTranspose (t + 1) F.Carrier).toMonoidHom
      (GeneralLinear.inverseTranspose (t + 1) F.Carrier).surjective
  have htπ₀d : F.canonicalTopologicalData.IsTempered (inverseTransposePullback π₀) :=
    F.canonicalTopologicalData.isTempered_comp_continuousMulEquiv π₀
      (F.canonicalTopologicalData.generalLinearInverseTranspose (r + 1)) ha
  have htσ₀d : F.canonicalTopologicalData.IsTempered (inverseTransposePullback σ₀) :=
    F.canonicalTopologicalData.isTempered_comp_continuousMulEquiv σ₀
      (F.canonicalTopologicalData.generalLinearInverseTranspose (t + 1)) hb
  have hPd' : IsPadicSymmetricLPolynomial F (ψ.scale (-1)) νd.val
      (realPowerTwist (F.canonicalTopologicalData.determinantNorm (r + 1)) (-a)
        (inverseTransposePullback π₀))
      (realPowerTwist (F.canonicalTopologicalData.determinantNorm (t + 1)) (-b)
        (inverseTransposePullback σ₀)) Pdual := by
    rw [← inverseTransposePullback_realPowerTwist F, ← inverseTransposePullback_realPowerTwist F]
    exact (isPadicSymmetricLPolynomial_of_le htr).2 hPd
  have hfreed := analyticTemperedTwistLPolynomial_poleFree F (ψ.scale (-1)) νd
    (inverseTransposePullback π₀) (inverseTransposePullback σ₀) hiπ₀d htπ₀d hiσ₀d htσ₀d
    (-a) (-b) hPd'
  have hq : (1 : ℝ) < F.canonicalTopologicalData.residueCardinality := by
    exact_mod_cast F.canonicalTopologicalData.residueCardinality_gt_one
  have hq0 : (0 : ℝ) < F.canonicalTopologicalData.residueCardinality := by linarith
  refine hasNoReflectedCommonZero_of_radii (Real.rpow_nonneg hq0.le _) ?_ hfree hfreed
  rw [mul_assoc, ← Real.rpow_add hq0, ← neg_add, add_neg_cancel, Real.rpow_zero, mul_one]
  exact hq

end Langlands.Global.GLPoleRegion
