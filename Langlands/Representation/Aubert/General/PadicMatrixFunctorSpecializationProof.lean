import Langlands.Representation.Aubert.General.PadicMatrixFunctorSpecializationStatement

/-! # Specialization of the local-field matrix functors to p-adic fields: proof -/

noncomputable section

universe u v

namespace Langlands.Aubert.General.RationalPointFamily.GL

/-- The local-field matrix functors of `T.toLocalFieldData` are the p-adic
matrix functors of `T`, they preserve finite length and finite-length short
exact sequences, and their maps on the finite-length Grothendieck groups are
`Parabolic.normalizedInductionK0` and `Parabolic.normalizedJacquetK0`. -/
theorem padicMatrixFunctorSpecialization :
    PadicMatrixFunctorSpecializationStatement.{u, v} := by
  intro p _ F T n B
  let := T.topology
  have h := Langlands.Parabolic.normalizedParabolicFiniteLength.{u, max (u + 1) v} F T
  refine ⟨rfl, rfl, h.1 n B,
    Langlands.Parabolic.FiniteLengthGrothendieckAssembly.normalizedInductionFunctor_preservesShortExact
      F T B,
    h.2 n B,
    Langlands.Parabolic.FiniteLengthGrothendieckAssembly.normalizedJacquetFunctor_preservesShortExact
      F T B, ?_⟩
  intro hi hix hr hrx
  exact ⟨rfl, rfl⟩

end Langlands.Aubert.General.RationalPointFamily.GL
