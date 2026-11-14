import Langlands.Algebra.SemilocalFiniteAlgebra
import Langlands.GroupScheme.Reductive.PicardTrivialQuasiSplitInnerFormStatement
import Langlands.GroupScheme.Reductive.SemilocalQuasiSplitInnerFormStatement

/-! # Reduction of semi-local quasi-split inner forms to Picard-trivial bases -/

universe u

namespace Langlands.GroupScheme

/-- The Picard-trivial-base theorem implies the unchanged semi-local theorem. -/
theorem reductiveSemilocalQuasiSplitInnerFormStatement_of_picardTrivial
    (h : ReductivePicardTrivialQuasiSplitInnerFormStatement.{u}) :
    ReductiveSemilocalQuasiSplitInnerFormStatement.{u} := by
  intro R _ hR
  let : Finite (MaximalSpectrum R) := hR
  apply h.1 R
  intro A _ _ _ _
  exact Algebra.finiteAlgebrasHaveTrivialPicard_of_semilocal R A

end Langlands.GroupScheme
