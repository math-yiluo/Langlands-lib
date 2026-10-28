import Langlands.Representation.Classification.WholeLeviTemperedFactorizationStatement
import Langlands.Representation.Classification.RelativeCosocleAdmissibilityProof
import Langlands.Representation.CuspidalSupport.LeviAdmissibleFactorizationProof
import Langlands.Representation.Induction.InnerLeviTransport
import Langlands.Representation.Classification.BlockTensorTemperedProof

namespace Langlands

universe uF uV

/-- Every irreducible analytically tempered whole-Levi representation factors
into irreducible admissible tempered blocks in its original carrier universe. -/
theorem glWholeLeviTemperedFactorization :
    GLWholeLeviTemperedFactorizationStatement.{uF, uV} := by
  intro p _ F T
  let := T.topology
  intro n hn B σ hσ htemp
  have hadm : IsAdmissible σ.ρ := htemp.isAdmissible
  let σsmooth : SmoothRep.{0, uF, uV} ℂ (B.Levi F.Carrier) :=
    SmoothRep.of σ.ρ hadm.1
  obtain ⟨A, hAi, hAa, ⟨e⟩⟩ :=
    CuspidalSupport.padicLeviAdmissibleFactorization.{uF, uV}
      p F T n hn B σsmooth hσ hadm
  have htensor : RelativeRegularComparison.IsLeviTempered T B
      (Rep.of (B.blockTensor (fun i => (A i).representation))) :=
    (T.isLeviTempered_iff_of_equiv B e).mp htemp
  refine ⟨A, hAi, hAa, ?_, ⟨e⟩⟩
  exact (glBlockTensorTempered.{uF, uV} p F T n hn B
    (fun i => A i) (fun i => (A i).representation) hAi hAa).mpr htensor

end Langlands
