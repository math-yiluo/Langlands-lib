import Langlands.Representation.CuspidalSupport.AssociationAssembly
import Langlands.Representation.CuspidalSupport.AssociationForwardHomProof
import Langlands.Representation.CuspidalSupport.AssociationForwardFactorsProof
import Langlands.Representation.CuspidalSupport.AssociationLawsProof
import Langlands.Representation.CuspidalSupport.AssociationReverseProof
import Langlands.Representation.CuspidalSupport.NormalizedCuspidalInductionLengthProof

/-! The three equivalences characterizing association of irreducible cuspidal
Levi induction, for every rank and independent carrier universes. -/

namespace Langlands.CuspidalSupport

universe uF uV uW

/-- Association is equivalent to nonzero Hom, matching actual Jordan–Hölder
factors with multiplicity, and a common actual irreducible subquotient. -/
theorem cuspidalInductionAssociation
    (p : ℕ) [Fact p.Prime] (F : PadicField.{uF} p)
    (T : F.TopologicalData) (n : ℕ) :
    CuspidalInductionAssociationTheorem.{uF, uV, uW} F T n :=
  AssociationAssembly.allRanks F T n
    associatedCuspidalInductionHomTheorem.{uF, uV, uW}
    associatedCuspidalInductionHomTheorem.{uF, uV, uV}
    representationAssociationReflexivity
    associatedCuspidalInductionFactorsTheorem.{uF, uV, uW}
    (fun m _ => cuspidalInductionLength.{uF, uW} F T m)
    (fun m _ => cuspidalInductionReverseAssociation.{uF, uV, uW} p F T m)

end Langlands.CuspidalSupport
