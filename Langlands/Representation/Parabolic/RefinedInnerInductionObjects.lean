import Langlands.Representation.Parabolic.OrderedRefinementTensorInduction

/-! # Smooth objects for normalized induction inside refined blocks -/

noncomputable section

namespace Langlands.CuspidalSupport

open GeneralLinear Parabolic

universe uF uV

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p) (T : F.TopologicalData)

/-- The actual smooth objects for normalized induction inside each refined
block of a common outer Levi. -/
def refinedInnerInductionObjects {r : ℕ} (D : BlockShape r)
    (S : Langlands.Geometric.BlockRefinement D)
    (C : RefinedInductionTensor.Factors.{uF,uV} F T D S) :
    letI := T.topology
    ∀ m, SmoothRep.{0,uF,max uF uV} ℂ (GeneralLinear (D.size m) F.Carrier) :=
  letI := T.topology
  fun m => SmoothRep.of (RefinedInductionTensor.blockRepresentations F T D S C m)
    (T.isSmooth_normalizedParabolicInduced (S m) (C m).representation)

end Langlands.CuspidalSupport
