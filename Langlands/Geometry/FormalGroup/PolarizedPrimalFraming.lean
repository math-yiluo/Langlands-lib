import Langlands.Geometry.FormalGroup.LocalQuasiIsogenyGroupoid
import Langlands.Geometry.FormalGroup.PolarizedFramedHeight
import Langlands.Geometry.FormalGroup.PolarizedRationalSectionIso
import Langlands.Geometry.FormalGroup.RationalIdempotentImage
import Langlands.Geometry.FormalGroup.SplitOrderFormalSummand

/-! # The actual primal rigidifier on affine split polarized objects -/

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

/-- Take the actual invertible rational framing on the ordinary division factor. -/
def primalFraming : RationalSectionIso ℚ_[prime] M N (reducedTop T) :=
  A.restrictSectionIso B X.localFraming.toSectionIso (by
    rw [LocalQuasiIsogeny.toSectionIso_hom, localFraming_val]
    exact X.commutes (0, 1))

@[simp]
theorem primalFraming_hom :
    (X.primalFraming A B).hom = A.restrictSection B X.rho := by
  change A.restrictSection B X.localFraming.toSectionIso.hom = _
  rw [LocalQuasiIsogeny.toSectionIso_hom, localFraming_val]

/-- Restricting the actual rigidifier also restricts its order-linearity. -/
theorem primalFraming_orderLinear :
    RationalSection.IsOrderLinear A.order B.order (X.primalFraming A B).hom := by
  intro b
  rw [primalFraming_hom]
  let E := (source (frame := frame) (T := T)).order
  let f := E.action (0, b)
  let g := X.reducedTarget.order.action (0, b)
  have hf : RationalSection.comp (RationalSection.ofHom (F := ℚ_[prime]) f ⊤)
      (RationalSection.ofHom E.divisionProjector ⊤) =
      RationalSection.comp (RationalSection.ofHom E.divisionProjector ⊤)
        (RationalSection.ofHom f ⊤) := by
    rw [RationalSection.comp_ofHom, RationalSection.comp_ofHom]
    exact congrArg (fun h => RationalSection.ofHom h ⊤)
      ((E.action_comp_divisionProjector b).trans (E.divisionProjector_comp_action b).symm)
  change RationalSection.comp (A.restrictSection B X.rho)
      (RationalSection.ofHom (A.restrictHom A f) ⊤) =
    RationalSection.comp (RationalSection.ofHom (B.restrictHom B g) ⊤)
      (A.restrictSection B X.rho)
  rw [← A.restrictSection_ofHom, ← B.restrictSection_ofHom,
    ← A.restrictSection_comp A B _ _ hf, X.commutes (0, b),
    A.restrictSection_comp B B _ _ (X.commutes (0, 1))]

/-- The raw p-height of the rigidifier on the actual primal images. -/
def HasPrimalFramingHeight (h : reducedTop T → ℤ) : Prop :=
  RationalSection.HasHeightFunction (prime : ℤ_[prime]) prime (X.primalFraming A B).hom h

end Langlands.FormalGroup.PolarizedFramedAffinePoint
