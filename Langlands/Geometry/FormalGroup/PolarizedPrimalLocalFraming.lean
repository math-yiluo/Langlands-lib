import Langlands.Geometry.FormalGroup.IdempotentLocalQuasiIsogeny
import Langlands.Geometry.FormalGroup.PolarizedPrimalFraming

/-! # Actual local quasi-isogeny of the split primal rigidifier -/

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
variable {M : ModuleLaw ℤ_[prime] ((Nilp.reductionFunctor W π).obj T).obj σ}
variable {N : ModuleLaw ℤ_[prime] ((Nilp.reductionFunctor W π).obj T).obj τ}
variable (A : (source (frame := frame) (T := T)).order.DivisionImage M)
variable (B : X.reducedTarget.order.DivisionImage N)

/-- The restriction is a local quasi-isogeny of the actual scalar-divisible primal laws. -/
def primalLocalFraming : LocalQuasiIsogeny ℚ_[prime] (prime : ℤ_[prime]) M N (reducedTop T) :=
  A.restrictLocalQuasiIsogeny B PadicInt.irreducible_p X.localFraming (by
    rw [localFraming_val]
    exact X.commutes (0, 1))

@[simp]
theorem primalLocalFraming_val : (X.primalLocalFraming A B).val = A.restrictSection B X.rho := by
  change A.restrictSection B X.localFraming.val = _
  rw [localFraming_val]

/-- The quasi-isogeny gives the same pair of rational sections as `primalFraming`. -/
theorem primalLocalFraming_toSectionIso :
    (X.primalLocalFraming A B).toSectionIso = X.primalFraming A B := by
  apply RationalSectionIso.ext
  rw [LocalQuasiIsogeny.toSectionIso_hom, primalLocalFraming_val, primalFraming_hom]

/-- The forward local quasi-isogeny is linear for the induced division order actions. -/
theorem primalLocalFraming_orderLinear :
    RationalSection.IsOrderLinear A.order B.order (X.primalLocalFraming A B).val := by
  rw [← LocalQuasiIsogeny.toSectionIso_hom, primalLocalFraming_toSectionIso]
  exact X.primalFraming_orderLinear A B

end Langlands.FormalGroup.PolarizedFramedAffinePoint
