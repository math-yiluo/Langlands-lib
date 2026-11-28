import Langlands.Representation.Aubert.General.RationalSupercuspidalInductionExtractionInputsProof
import Langlands.Representation.Aubert.General.RationalCuspidalExtractionFromSpecialVertex
import Langlands.Representation.CuspidalSupport.RationalCuspidalInertiaDecompositionReduction
import Langlands.BruhatTits.SpecialCompact.JointBasisProof

/-! # Finite length of actual supercuspidal induction (Renard VI.5.4) -/

universe u uV

namespace Langlands.Aubert.General.RationalPointFamily

/-- The finite-length assertion of Renard, Théorème VI.5.4, on the actual
standard rational-point families of a connected reductive group over a
nonarchimedean local field: the full-parabolic Haar-normalized induction of an
irreducible inside-Levi cuspidal representation of an actual standard Levi has
finite length. The joint special-compact basis gives the special-vertex inputs,
these give the geometric filtration and the proper-standard induction exclusion,
and those two inputs give the finite length. -/
theorem rationalSupercuspidalInductionFiniteLength :
    RationalSupercuspidalInductionFiniteLengthStatement.{u, uV} :=
  rationalSupercuspidalInductionFiniteLengthFromExtractionInputs
    (rationalCuspidalExtractionInputs_of_specialVertexInputs
      (CuspidalSupport.rationalSpecialVertexCompactInputs_of_jointBasis
        BruhatTits.SpecialCompact.jointSpecialCompactBasisExistence))

end Langlands.Aubert.General.RationalPointFamily
