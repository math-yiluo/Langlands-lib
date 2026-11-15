import Langlands.Representation.Aubert.General.CanonicalRationalTheorem17ReductionStatements
import Langlands.Representation.Aubert.General.CanonicalRationalTargetBridgesProof
import Langlands.Representation.Aubert.General.RationalInductionK0Assembly
import Langlands.Representation.Aubert.General.RationalGeometricK0Expansion

/-! # Proof of the reduction of canonical induction compatibility -/

universe u v

namespace Langlands.Aubert.General.RationalPointFamily

/-- Induced K0 Weyl conjugacy implies Théorème 1.7 (2) for the canonical
actual families. -/
theorem canonicalRationalInductionCompatibilityReduction :
    CanonicalRationalInductionCompatibilityReductionStatement.{u, v} := by
  intro hWeyl
  have hcompat : RationalInductionCompatibilityStatement.{u, v} :=
    rationalInductionCompatibility_of_expansion_and_inducedWeyl.{u, v}
      ⟨rationalGeometricK0Expansion.{u, v}, hWeyl⟩
  exact canonicalRationalTargetBridges.{u, v}.2.1 hcompat

end Langlands.Aubert.General.RationalPointFamily
