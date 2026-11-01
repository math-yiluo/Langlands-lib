import Langlands.Representation.Smooth.FiniteLengthGrothendieckTransport
import Langlands.Representation.Geometric.FlattenedLevi

/-! Exact finite-length smooth K0 in the actual flattened Levi coordinates. -/

noncomputable section

namespace Langlands.Geometric

open GeneralLinear SmoothRep

universe uF uV

variable (F : Type uF) [Field F] [TopologicalSpace F] [IsTopologicalRing F]
  {n : ℕ} (B : BlockShape n) (S : BlockRefinement B)

/-- The existing actual flattened coordinate map induces an integer-linear
equivalence from refined-subgroup K0 to flattened-product K0. -/
def flattenedLeviK0 :
    SmoothRep.FiniteLengthGrothendieckGroup.{0, uF, max uF uV} ℂ
        (refinedLevi F B S) ≃ₗ[ℤ]
      (B.flatten S).FiniteLengthGrothendieckGroup.{uV, uF} F :=
  SmoothRep.FiniteLengthGrothendieckGroup.pullbackEquiv
    (flattenedLeviEquivContinuous F B S)

/-- The forward map is pullback along the literal flattened coordinate map. -/
theorem flattenedLeviK0_toLinearMap :
    (flattenedLeviK0.{uF, uV} F B S).toLinearMap =
      SmoothRep.FiniteLengthGrothendieckGroup.pullback
        (flattenedLeviEquivContinuous F B S) := rfl

/-- An actual refined representation becomes its literal flattened pullback,
with any proof of the output's finite length. -/
theorem flattenedLeviK0_finiteLengthClass
    (A : SmoothRep.{0, uF, max uF uV} ℂ (refinedLevi F B S))
    (hA : A.HasFiniteLength)
    (hOut : (SmoothRep.pullback (flattenedLeviEquivContinuous F B S) A).HasFiniteLength) :
    flattenedLeviK0.{uF, uV} F B S
        (SmoothRep.FiniteLengthGrothendieckGroup.ofRepresentation A hA) =
      (B.flatten S).finiteLengthClass F
        (SmoothRep.pullback (flattenedLeviEquivContinuous F B S) A) hOut :=
  SmoothRep.FiniteLengthGrothendieckGroup.pullback_ofRepresentation
    (flattenedLeviEquivContinuous F B S) A hA hOut

/-- The inverse coordinate change is actual pullback by the inverse
continuous flattened-Levi equivalence. -/
theorem flattenedLeviK0_symm_finiteLengthClass
    (A : SmoothRep.{0, uF, max uF uV} ℂ ((B.flatten S).Levi F))
    (hA : A.HasFiniteLength)
    (hOut : (SmoothRep.pullback
      (flattenedLeviEquivContinuous F B S).symm A).HasFiniteLength) :
    (flattenedLeviK0.{uF, uV} F B S).symm
        ((B.flatten S).finiteLengthClass F A hA) =
      SmoothRep.FiniteLengthGrothendieckGroup.ofRepresentation
        (SmoothRep.pullback (flattenedLeviEquivContinuous F B S).symm A) hOut :=
  SmoothRep.FiniteLengthGrothendieckGroup.pullback_ofRepresentation
    (flattenedLeviEquivContinuous F B S).symm A hA hOut

end Langlands.Geometric
