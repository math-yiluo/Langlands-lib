import Mathlib.LinearAlgebra.Charpoly.Basic
import Mathlib.LinearAlgebra.Charpoly.ToMatrix
import Langlands.Algebra.ReducedCharpoly
import Langlands.Algebra.LocalDivisionUnramifiedSubfield

/-! Minimal-polynomial degree bounds in central division algebras. -/

noncomputable section

namespace Langlands.CentralDivision

open Langlands.CentralSimple
open _root_.Polynomial
open ValuativeRel

universe u

variable (K D : Type u) [Field K] [DivisionRing D] [Algebra K D]
  [FiniteDimensional K D] [Algebra.IsCentral K D]

/-- The actual reduced characteristic polynomial annihilates an original division element. -/
theorem aeval_reducedCharpoly (a : D) :
    Polynomial.aeval a (reducedCharpoly K D a) = 0 := by
  have h := Algebra.aeval_self_charpoly_lmul (R := K) a
  rw [← LinearMap.charpoly_toMatrix _ (Module.finBasis K D)] at h
  change Polynomial.aeval a (Algebra.leftMulMatrix (Module.finBasis K D) a).charpoly = 0 at h
  rw [charpoly_leftMulMatrix_eq_reducedCharpoly_pow, map_pow] at h
  exact eq_zero_of_pow_eq_zero h

/-- The original minimal polynomial divides the canonical reduced characteristic polynomial. -/
theorem minpoly_dvd_reducedCharpoly (a : D) :
    minpoly K a ∣ reducedCharpoly K D a :=
  minpoly.dvd K a (aeval_reducedCharpoly K D a)

/-- The canonical polynomial factor complementary to the original minimal polynomial. -/
def reducedCharpolyMinpolyQuotient (a : D) : Polynomial K :=
  reducedCharpoly K D a / minpoly K a

/-- The complementary factor gives an exact factorization over the original center. -/
theorem minpoly_mul_reducedCharpolyMinpolyQuotient (a : D) :
    minpoly K a * reducedCharpolyMinpolyQuotient K D a = reducedCharpoly K D a :=
  EuclideanDomain.mul_div_cancel' (minpoly.ne_zero (Algebra.IsIntegral.isIntegral a))
    (minpoly_dvd_reducedCharpoly K D a)

/-- Every original division element has minimal-polynomial degree at most the reduced degree. -/
theorem minpoly_natDegree_le_reducedDegree (a : D) :
    (minpoly K a).natDegree ≤ reducedDegree K D := by
  rw [← reducedCharpoly_natDegree K D a]
  exact Polynomial.natDegree_le_of_dvd (minpoly_dvd_reducedCharpoly K D a)
    (reducedCharpoly_monic K D a).ne_zero

/-- Its actual commutative singleton adjoin has degree at most the reduced degree. -/
theorem residueGeneratorSubalgebra_finrank_le_reducedDegree (a : D) :
    letI := residueGeneratorField K D a
    Module.finrank K (residueGeneratorSubalgebra K D a) ≤ reducedDegree K D := by
  let := residueGeneratorField K D a
  rw [residueGeneratorSubalgebra_finrank]
  exact minpoly_natDegree_le_reducedDegree K D a

/-- In the local case the original actual residue extension has at most the reduced degree. -/
theorem localDivisionResidue_finrank_le_reducedDegree
    [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K] :
    letI := localDivisionResidueField K D
    letI := localDivisionResidueAlgebra K D
    Module.finrank 𝓀[K]
      (DivisionValuation.Residue (localReducedNormValuation K D)) ≤ reducedDegree K D := by
  let := localDivisionResidueField K D
  let := localDivisionResidueAlgebra K D
  obtain ⟨b, _, _, hdim⟩ := exists_localDivision_fullResidue_degree_subfield K D
  let := residueGeneratorField K D (b : D)
  rw [← hdim]
  exact residueGeneratorSubalgebra_finrank_le_reducedDegree K D (b : D)

end Langlands.CentralDivision
