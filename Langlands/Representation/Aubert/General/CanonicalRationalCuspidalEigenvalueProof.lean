import Langlands.Representation.Aubert.General.CanonicalRationalTargetBridgesProof
import Langlands.Representation.Aubert.General.RationalCuspidalEigenvalueProof

/-! # Proof of the canonical cuspidal eigenvalue -/

universe u v

namespace Langlands.Aubert.General.RationalPointFamily

/-- Aubert's cuspidal eigenvalue for the canonical actual operator. -/
theorem canonicalRationalCuspidalEigenvalue :
    CanonicalRationalCuspidalEigenvalueStatement.{u, v} :=
  canonicalRationalCuspidalEigenvalue_of_rational.{u, v}
    rationalCuspidalEigenvalue.{u, v}

end Langlands.Aubert.General.RationalPointFamily
