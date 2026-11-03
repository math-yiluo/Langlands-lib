import Langlands.GroupScheme.Absolute.GeneralLinearSolvableStabilizerProof

/-! # Exact proof target for a proper `GL_N`-scheme with solvable point stabilizers -/

universe u

namespace Langlands.GroupScheme

/-- The published proper `GL_N` action and solvable-stabilizer theorem, at every universe. -/
theorem generalLinearSolvableStabilizer_proof :
    GeneralLinearSolvableStabilizerStatement.{u} :=
  generalLinearSolvableStabilizer.{u}

end Langlands.GroupScheme
