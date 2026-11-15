import Langlands.Representation.Aubert.General.CanonicalRationalTheorem17ReductionStatements
import Langlands.Representation.Aubert.General.CanonicalRationalTargetBridgesProof
import Langlands.Representation.Aubert.General.RationalTermTransitivityProof

/-! # Proof of the reduction of canonical involutivity -/

universe u v

namespace Langlands.Aubert.General.RationalPointFamily

/-- Induced K0 Weyl conjugacy implies Théorème 1.7 (3) for the canonical
actual operator. -/
theorem canonicalRationalInvolutivityReduction :
    CanonicalRationalInvolutivityReductionStatement.{u, v} := by
  intro hWeyl
  have hInv : RationalInvolutivityStatement.{u, v} :=
    rationalInvolutivityStatement_of_inducedK0WeylConjugacy.{u, v} hWeyl
  exact canonicalRationalTargetBridges.{u, v}.2.2.2.1 hInv

end Langlands.Aubert.General.RationalPointFamily
