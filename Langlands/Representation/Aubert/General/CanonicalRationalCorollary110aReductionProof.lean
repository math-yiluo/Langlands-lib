import Langlands.Representation.Aubert.General.CanonicalRationalTheorem17ReductionStatements
import Langlands.Representation.Aubert.General.CanonicalRationalTargetBridgesProof
import Langlands.Representation.Aubert.General.RationalCorollary110aAssembly

/-! # Proof of the reduction of canonical Corollaire 1.10 (a) -/

universe u v

namespace Langlands.Aubert.General.RationalPointFamily

/-- Induced K0 Weyl conjugacy implies Corollaire 1.10 (a) for the canonical
actual families. -/
theorem canonicalRationalCorollary110aReduction :
    CanonicalRationalCorollary110aReductionStatement.{u, v} := by
  intro hWeyl
  have h110a : RationalCorollary110aStatement.{u, v} :=
    rationalCorollary110aStatement_of_inducedK0WeylConjugacy.{u, v} hWeyl
  exact canonicalRationalTargetBridges.{u, v}.2.2.2.2.2.1 h110a

end Langlands.Aubert.General.RationalPointFamily
