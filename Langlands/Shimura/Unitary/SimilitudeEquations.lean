import Langlands.Shimura.Unitary.SimilitudeCoordinates

/-! # The defining equations of the similitude coordinate algebra -/

universe r u v w

namespace Langlands.Shimura.AlgebraInvolution

open scoped TensorProduct
open MvPolynomial

variable {R : Type r} {A : Type u} [CommRing R] [Ring A] [Algebra R A]
variable {ι : Type v} [Fintype ι] (b : Module.Basis ι R A)
variable (σ : AlgebraInvolution R A)
variable {S : Type w} [CommRing S] [Algebra R S]

/-- The four defining equations after specializing the polynomial variables
along an algebra homomorphism. The multiplier remains a recorded scalar. -/
def SimilitudePolynomialEquations
    (ψ : MvPolynomial (SimilitudeVariable ι) R →ₐ[R] S) : Prop :=
  changeCoefficients ψ (genericUnit b) * changeCoefficients ψ (genericUnitInv b) = 1 ∧
  changeCoefficients ψ (genericUnitInv b) * changeCoefficients ψ (genericUnit b) = 1 ∧
  changeCoefficients ψ (genericUnit b) *
      σ.baseChange S (changeCoefficients ψ (genericUnit b)) =
    algebraMap S (S ⊗[R] A) (ψ (X SimilitudeVariable.multiplier)) ∧
  ψ (X SimilitudeVariable.multiplier) * ψ (X SimilitudeVariable.multiplierInv) = 1

/-- Vanishing of the defining ideal is exactly the specialized equations. -/
theorem similitudeIdeal_le_ker_iff
    (ψ : MvPolynomial (SimilitudeVariable ι) R →ₐ[R] S) :
    σ.similitudeIdeal b ≤ RingHom.ker ψ ↔ σ.SimilitudePolynomialEquations b ψ := by
  constructor
  · intro h
    have hz (x : MvPolynomial (SimilitudeVariable ι) R ⊗[R] A)
        (hx : ∀ i, coordinate b x i ∈ σ.similitudeIdeal b) :
        changeCoefficients ψ x = 0 := by
      apply ext_coordinate b
      intro i
      rw [coordinate_changeCoefficients, coordinate_zero]
      exact RingHom.mem_ker.mp (h (hx i))
    refine ⟨?_, ?_, ?_, ?_⟩
    · have e := hz (genericUnit b * genericUnitInv b - 1)
        (fun i => Ideal.subset_span (Or.inl (Or.inl (Or.inl ⟨i, rfl⟩))))
      rwa [map_sub, _root_.map_mul, _root_.map_one, sub_eq_zero] at e
    · have e := hz (genericUnitInv b * genericUnit b - 1)
        (fun i => Ideal.subset_span (Or.inl (Or.inl (Or.inr ⟨i, rfl⟩))))
      rwa [map_sub, _root_.map_mul, _root_.map_one, sub_eq_zero] at e
    · have e := hz (genericUnit b * σ.baseChange _ (genericUnit b) -
          algebraMap _ _ (X SimilitudeVariable.multiplier))
        (fun i => Ideal.subset_span (Or.inl (Or.inr ⟨i, rfl⟩)))
      rwa [map_sub, _root_.map_mul, changeCoefficients_involution,
        changeCoefficients_scalar, sub_eq_zero] at e
    · have e := RingHom.mem_ker.mp (h (Ideal.subset_span (Or.inr rfl)))
      simpa only [map_sub, _root_.map_mul, _root_.map_one, sub_eq_zero] using e
  · rintro ⟨h₁, h₂, h₃, h₄⟩
    exact σ.similitudeIdeal_le_ker b ψ h₁ h₂ h₃ h₄

end Langlands.Shimura.AlgebraInvolution
