import Langlands.LocalField.PadicBridge
import Langlands.AllField.Representation.Induction.Parabolic
import Langlands.AllField.Representation.Jacquet.Parabolic
import Langlands.Representation.Aubert.AlternatingOperator

/-! # Specialization of the local-field matrix functors to p-adic fields -/

noncomputable section

universe u v

namespace Langlands.Aubert.General.RationalPointFamily.GL

open SmoothRep

/-- Forgetting the specified p-adic base extension preserves both actual
normalized matrix functors and their maps on the exact finite-length
Grothendieck groups. -/
def PadicMatrixFunctorSpecializationStatement : Prop :=
  ∀ {p : ℕ} [Fact p.Prime] (F : PadicField.{u} p) (T : F.TopologicalData)
    (n : ℕ) (B : Langlands.GeneralLinear.BlockShape n),
    letI := T.topology
    let i := T.toLocalFieldData.normalizedParabolicInductionFunctor.{u, max (u + 1) v} B
    let r := T.toLocalFieldData.normalizedJacquetFunctor.{u, max (u + 1) v} B
    i = T.normalizedParabolicInductionFunctor.{u, max (u + 1) v} B ∧
      r = T.normalizedJacquetFunctor.{u, max (u + 1) v} B ∧
      PreservesFiniteLength i ∧ PreservesFiniteLengthShortExact i ∧
      PreservesFiniteLength r ∧ PreservesFiniteLengthShortExact r ∧
      ∀ (hi : PreservesFiniteLength i) (hix : PreservesFiniteLengthShortExact i)
        (hr : PreservesFiniteLength r) (hrx : PreservesFiniteLengthShortExact r),
        FiniteLengthGrothendieckGroup.map i hi hix =
          Parabolic.normalizedInductionK0.{u, max (u + 1) v} F T B ∧
        FiniteLengthGrothendieckGroup.map r hr hrx =
          Parabolic.normalizedJacquetK0.{u, max (u + 1) v} F T B

end Langlands.Aubert.General.RationalPointFamily.GL
