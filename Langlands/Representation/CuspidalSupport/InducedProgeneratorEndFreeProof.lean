import Langlands.BruhatTits.SpecialCompact.JointBasisProof
import Langlands.Representation.CuspidalSupport.InducedProgeneratorEndFreeReduction

/-! # Freeness of the induced progenerator endomorphism ring (Renard VI.10.4) -/

universe u v

namespace Langlands.Aubert.General.RepresentedParabolic

/-- The first Lemma of Renard VI.10.4, including injectivity of induction on endomorphisms,
the finite basis over the Levi progenerator endomorphism ring, and the finite basis over
its centre. -/
theorem inducedProgeneratorEndFree : InducedProgeneratorEndFreeStatement.{u, v} :=
  inducedProgeneratorEndFree_of_jointSpecialCompact
    BruhatTits.SpecialCompact.jointSpecialCompactBasisExistence

end Langlands.Aubert.General.RepresentedParabolic
