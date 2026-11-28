import Langlands.AllFieldBZ.Representation.Derivative.PartialDerivativeTensorStatement

/-! Partial derivatives on actual exterior tensor products over local fields. -/

open CategoryTheory

namespace Langlands.AllFieldBZ.Derivative

open Langlands.Derivative.PartialTensor (exteriorFunctor firstFactorFunctor)

universe uF uV

/-- The partial derivative differentiates the right factor in top order and
keeps the left action on the resulting tensor. The comparison is natural in
both smooth representations and includes rank zero. -/
def PartialDerivativeExteriorTensorStatement : Prop :=
  ∀ (F : LocalFieldPackage.{uF}) (T : F.TopologicalData),
    letI := T.topology
    ∀ (ψ : @HarmonicAnalysis.UnitaryAdditiveCharacter F.Carrier _ T.topology) (a b : ℕ),
      Nonempty
        (exteriorFunctor.{uF,uV} ⋙ partialDerivative T ψ a b ≅
          (𝟭 _).prod (topDerivative T ψ b) ⋙ firstFactorFunctor)

end Langlands.AllFieldBZ.Derivative
