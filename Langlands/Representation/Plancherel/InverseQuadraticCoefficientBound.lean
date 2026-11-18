import Langlands.Representation.Unitary.CornerFormGluingProof
import Langlands.Representation.Plancherel.PolynomialPositiveFormBound

/-! # Bounded inverse quadratic coefficients detected by a fixed functional -/

noncomputable section

open scoped NNReal

namespace Langlands.Plancherel.UnramifiedOperatorFamily

universe uG uI uV uW

variable {G : Type uG} [Group G] [TopologicalSpace G]
  {I : Type uI} {ν : I → (G →* ℝ≥0ˣ)}
  {V : Type uV} [AddCommGroup V] [Module ℂ V]
  {W : Type uW} [AddCommGroup W] [Module ℂ W]
  {Ω : Set (unramifiedCharacters ν)} {A : Ω → V →ₗ[ℂ] W}

/-- The inverse positive quadratic coefficient of a continued vector family. -/
def inverseQuadraticCoefficient (p : RationalOperatorContinuationData Ω A)
    (v : V) (c : InnerProductSpace.Core ℂ W) (z : p.regularRegion) : ℂ :=
  (c.inner (p.continuedOperator z v) (p.continuedOperator z v))⁻¹

omit [Group G] [TopologicalSpace G] in
/-- A Hermitian diagonal is its real part. -/
theorem core_inner_self_eq_re (c : InnerProductSpace.Core ℂ W) (w : W) :
    c.inner w w = ((c.inner w w).re : ℂ) :=
  CornerFormGluing.inner_self_eq_ofReal_re c w

/-- A constant nonzero functional value on the continued family makes its
inverse positive quadratic coefficient uniformly bounded on the entire regular
region. The finite-dimensionality needed for the estimate comes from the
polynomial numerator, not from the ambient carrier. -/
theorem exists_inverseQuadraticCoefficient_norm_bound
    (p : RationalOperatorContinuationData Ω A) (v : V)
    (c : InnerProductSpace.Core ℂ W) (ℓ : W →ₗ[ℂ] ℂ)
    (a : ℂ) (ha : a ≠ 0)
    (hconst : ∀ z : p.regularRegion, ℓ (p.continuedOperator z v) = a) :
    ∃ B : ℝ, 0 < B ∧ ∀ z : p.regularRegion,
      ‖inverseQuadraticCoefficient p v c z‖ ≤ B := by
  obtain ⟨C, hC, hbound⟩ := exists_continuedOperator_functional_sq_bound p v c ℓ
  have ha2 : 0 < ‖a‖ ^ 2 := sq_pos_of_pos (norm_pos_iff.mpr ha)
  refine ⟨C / ‖a‖ ^ 2, div_pos hC ha2, fun z => ?_⟩
  have hb := hbound z
  rw [hconst z] at hb
  let r := (c.inner (p.continuedOperator z v) (p.continuedOperator z v)).re
  have hr : 0 < r := by
    have hn := c.re_inner_nonneg (p.continuedOperator z v)
    change ‖a‖ ^ 2 ≤ C * r at hb
    change 0 ≤ r at hn
    nlinarith
  have he := core_inner_self_eq_re c (p.continuedOperator z v)
  change c.inner (p.continuedOperator z v) (p.continuedOperator z v) = (r : ℂ) at he
  simp only [inverseQuadraticCoefficient, he, norm_inv, Complex.norm_real,
    Real.norm_eq_abs, abs_of_pos hr]
  apply (le_div_iff₀ ha2).mpr
  calc
    r⁻¹ * ‖a‖ ^ 2 ≤ r⁻¹ * (C * r) :=
      mul_le_mul_of_nonneg_left hb (inv_nonneg.mpr hr.le)
    _ = C := by rw [mul_left_comm, inv_mul_cancel₀ hr.ne', mul_one]

end Langlands.Plancherel.UnramifiedOperatorFamily
