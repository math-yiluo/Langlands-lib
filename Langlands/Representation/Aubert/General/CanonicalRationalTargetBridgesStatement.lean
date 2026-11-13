import Langlands.Representation.Aubert.General.CanonicalRationalTheorem17Targets

/-! # Existing rational-point Aubert targets imply their canonical forms (statement) -/

universe u v

namespace Langlands.Aubert.General.RationalPointFamily

/-- Each of the eight existing actual rational-point targets of Aubert Theorem 1.7,
Corollary 1.10 and the induced Weyl-conjugacy identity implies its canonical form.
The conjuncts are, in order: (1) contragredient commutation, (2a) induction
compatibility, (2b) Jacquet compatibility, (3) involutivity, (4) the cuspidal
eigenvalue, Corollary 1.10(a), Corollary 1.10(b) and induced Weyl conjugacy.
This is a proof target, not a theorem. -/
def CanonicalRationalTargetBridgesStatement : Prop :=
  (RationalContragredientCommutationStatement.{u, v} →
      CanonicalRationalContragredientCommutationStatement.{u, v}) ∧
    (RationalInductionCompatibilityStatement.{u, v} →
      CanonicalRationalInductionCompatibilityStatement.{u, v}) ∧
    (RationalJacquetCompatibilityStatement.{u, v} →
      CanonicalRationalJacquetCompatibilityStatement.{u, v}) ∧
    (RationalInvolutivityStatement.{u, v} →
      CanonicalRationalInvolutivityStatement.{u, v}) ∧
    (RationalCuspidalEigenvalueStatement.{u, v} →
      CanonicalRationalCuspidalEigenvalueStatement.{u, v}) ∧
    (RationalCorollary110aStatement.{u, v} →
      CanonicalRationalCorollary110aStatement.{u, v}) ∧
    (RationalCorollary110bStatement.{u, v} →
      CanonicalRationalCorollary110bStatement.{u, v}) ∧
    (RationalInducedK0WeylConjugacyStatement.{u, v} →
      CanonicalRationalInducedK0WeylConjugacyStatement.{u, v})

end Langlands.Aubert.General.RationalPointFamily
