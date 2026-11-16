import Langlands.Representation.Plancherel.RationalUnramifiedOperatorContinuation

/-! # Explicit inverses from two scalar composition identities -/

noncomputable section

open scoped NNReal

namespace Langlands.Plancherel

universe uG uI uV uW

namespace ScalarComposite

variable {V : Type uV} [AddCommGroup V] [Module ℂ V]
  {W : Type uW} [AddCommGroup W] [Module ℂ W]

/-- The proposed inverse is a displayed scalar multiple of the other map. -/
def inverse (c : ℂ) (S : W →ₗ[ℂ] V) : W →ₗ[ℂ] V :=
  c⁻¹ • S

/-- The first scalar composition identity supplies a left inverse. -/
theorem inverse_comp (R : V →ₗ[ℂ] W) (S : W →ₗ[ℂ] V)
    (c : ℂ) (hc : c ≠ 0) (hSR : S.comp R = c • LinearMap.id) :
    (inverse c S).comp R = LinearMap.id := by
  ext v
  have h := congrArg (fun T : V →ₗ[ℂ] V => T v) hSR
  change c⁻¹ • S (R v) = v
  change S (R v) = c • v at h
  rw [h, smul_smul, inv_mul_cancel₀ hc, one_smul]

/-- The second scalar composition identity supplies a right inverse. -/
theorem comp_inverse (R : V →ₗ[ℂ] W) (S : W →ₗ[ℂ] V)
    (c : ℂ) (hc : c ≠ 0) (hRS : R.comp S = c • LinearMap.id) :
    R.comp (inverse c S) = LinearMap.id := by
  ext w
  have h := congrArg (fun T : W →ₗ[ℂ] W => T w) hRS
  change R (c⁻¹ • S w) = w
  change R (S w) = c • w at h
  rw [map_smul, h, smul_smul, inv_mul_cancel₀ hc, one_smul]

/-- Both displayed scalar identities, with nonzero scalar, prove bijectivity.
No irreducibility statement is used. -/
theorem bijective (R : V →ₗ[ℂ] W) (S : W →ₗ[ℂ] V)
    (c : ℂ) (hc : c ≠ 0) (hSR : S.comp R = c • LinearMap.id)
    (hRS : R.comp S = c • LinearMap.id) :
    Function.Bijective R := by
  have hl : Function.LeftInverse (inverse c S) R :=
    fun v => congrArg (fun T : V →ₗ[ℂ] V => T v) (inverse_comp R S c hc hSR)
  have hr : Function.RightInverse (inverse c S) R :=
    fun w => congrArg (fun T : W →ₗ[ℂ] W => T w) (comp_inverse R S c hc hRS)
  exact ⟨hl.injective, hr.surjective⟩

/-- The explicit scalar formula is the inverse of the particular map `R`. -/
theorem inverse_eq_ofBijective (R : V →ₗ[ℂ] W) (S : W →ₗ[ℂ] V)
    (c : ℂ) (hc : c ≠ 0) (hRS : R.comp S = c • LinearMap.id)
    (hR : Function.Bijective R) :
    inverse c S = (LinearEquiv.ofBijective R hR).symm.toLinearMap := by
  ext w
  apply hR.injective
  calc
    R (inverse c S w) = w :=
      congrArg (fun T : W →ₗ[ℂ] W => T w) (comp_inverse R S c hc hRS)
    _ = R ((LinearEquiv.ofBijective R hR).symm w) :=
      ((LinearEquiv.ofBijective R hR).apply_symm_apply w).symm

end ScalarComposite

namespace UnramifiedOperatorFamily

variable {G : Type uG} [Group G] [TopologicalSpace G]
  {I : Type uI} {ν : I → (G →* ℝ≥0ˣ)}
  {V : Type uV} [AddCommGroup V] [Module ℂ V]
  {W : Type uW} [AddCommGroup W] [Module ℂ W]
  {Ω : Set (unramifiedCharacters ν)}

namespace RationalOperatorContinuationData

variable {A : Ω → V →ₗ[ℂ] W} (p : RationalOperatorContinuationData Ω A)
  (a b : unramifiedRegularFunctions ν)
  (hb : ∀ χ : Ω, b.val χ.val ≠ 0)

/-- Multiply a displayed operator presentation by the displayed regular ratio.
The product denominator is chosen for the entire operator. -/
def regularRatioSmul :
    RationalOperatorContinuationData Ω
      (fun χ => (a.val χ.val / b.val χ.val) • A χ) where
  denominator := b * p.denominator
  denominator_nonzero χ := mul_ne_zero (hb χ) (p.denominator_nonzero χ)
  numerator χ := a.val χ • p.numerator χ
  polynomial := p.polynomial.regular_smul a
  clears χ := by
    rw [p.clears χ]
    simp only [smul_smul, Subalgebra.coe_mul, Pi.mul_apply]
    congr 1
    field_simp [hb χ]

/-- This displayed presentation is regular precisely where its original
operator denominator and the new scalar denominator are nonzero. -/
@[simp]
theorem regularRatioSmul_regularRegion :
    (p.regularRatioSmul a b hb).regularRegion =
      {χ | b.val χ ≠ 0} ∩ p.regularRegion := by
  ext χ
  exact mul_ne_zero_iff

/-- The displayed continued value is the corresponding ratio times the
displayed continued operator. -/
theorem regularRatioSmul_continuedOperator
    (χ : ↥({χ | b.val χ ≠ 0} ∩ p.regularRegion)) :
    (p.regularRatioSmul a b hb).continuedOperator ⟨χ.val, by
        rw [regularRatioSmul_regularRegion]
        exact χ.property⟩ =
      (a.val χ.val / b.val χ.val) •
        p.continuedOperator ⟨χ.val, χ.property.2⟩ := by
  simp only [continuedOperator, regularRatioSmul, Subalgebra.coe_mul,
    Pi.mul_apply, smul_smul, mul_inv, div_eq_mul_inv]
  congr 1
  ring

/-- Inverting a displayed scalar ratio gives exactly the scalar-composite
inverse formula. Applying this identity as an inverse still requires the
two composition identities proved above. -/
theorem regularRatioSmul_continuedOperator_inverse
    (χ : ↥({χ | b.val χ ≠ 0} ∩ p.regularRegion)) :
    (p.regularRatioSmul a b hb).continuedOperator ⟨χ.val, by
        rw [regularRatioSmul_regularRegion]
        exact χ.property⟩ =
      ScalarComposite.inverse (b.val χ.val / a.val χ.val)
        (p.continuedOperator ⟨χ.val, χ.property.2⟩) := by
  rw [regularRatioSmul_continuedOperator]
  simp only [ScalarComposite.inverse, inv_div]

end RationalOperatorContinuationData

end UnramifiedOperatorFamily

end Langlands.Plancherel
