import Langlands.Geometry.FormalGroup.LocalQuasiIsogenyScalarHeight
import Langlands.Geometry.FormalGroup.PolarizedPrimalLocalFraming

/-! # Transfer of scalar-kernel height to a split primal target -/

noncomputable section

universe u

namespace Langlands.FormalGroup.PolarizedFramedAffinePoint

open ModuleLaw Langlands.Shimura

attribute [local instance] ModuleLaw.coefficientAlgebra ModuleLaw.coefficientScalarTower

variable {prime : ℕ} [Fact prime.Prime]
variable {W : Type} [CommRing W] [Algebra ℤ_[prime] W] {π : W}
variable {D : Type u} [Ring D] [Algebra ℤ_[prime] D]
variable {star : AlgebraInvolution ℤ_[prime] (Dᵐᵒᵖ × D)}
variable {frame : PolarizedOrderModule (Dᵐᵒᵖ × D) star (ResidueRing W π) (prime : ℤ_[prime])}
variable {T : Nilp.{0, 0} W π}
variable (X : PolarizedFramedAffinePoint prime π frame T)
variable {σ τ : Type} [Finite σ] [Finite τ]
variable {M : ModuleLaw ℤ_[prime] (ResidueRing W π) σ}
variable {N : ModuleLaw ℤ_[prime] T.obj τ}
variable (A : frame.order.DivisionImage M) (B : X.target.order.DivisionImage N)

/-- The original image laws give the primal local framing upon reduction and coefficient extension. -/
def primalLocalFramingFromImages :
    LocalQuasiIsogeny ℚ_[prime] (prime : ℤ_[prime])
      (M.map (frameCoefficientMap prime π T)) (N.map (Nilp.quotientO ℤ_[prime] T)) (reducedTop T) :=
  X.primalLocalFraming (A.map (frameCoefficientMap prime π T)) (B.map (Nilp.quotientO ℤ_[prime] T))

include A B in
/-- The actual scalar-kernel height of the primal target comes from the primal residue frame. -/
theorem primalTarget_hasPiHeight {H : ℕ} (hM : M.HasPiHeight (prime : ℤ_[prime]) prime H) :
    N.HasPiHeight (prime : ℤ_[prime]) prime H := by
  apply (B.isPiDivisible X.target.divisible).hasPiHeight_of_map_surjective (Nilp.quotientO ℤ_[prime] T)
  · change Function.Surjective (PrimeSpectrum.comap (Ideal.Quotient.mk (Nilp.reductionIdeal π T.obj)))
    apply (PrimeSpectrum.comap_quotientMk_bijective_of_le_nilradical _).surjective
    rw [Nilp.reductionIdeal, Ideal.span_singleton_le_iff_mem, mem_nilradical]
    exact T.property
  · exact (X.primalLocalFramingFromImages A B).target_hasPiHeight (hM.map (frameCoefficientMap prime π T))

end Langlands.FormalGroup.PolarizedFramedAffinePoint
