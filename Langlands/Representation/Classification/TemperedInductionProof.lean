import Langlands.Representation.Classification.TemperedInductionStatement
import Langlands.Representation.Classification.LeviTemperedUnitarityProof
import Langlands.Representation.Classification.TemperedInductionPreservationProof
import Langlands.Representation.Induction.UnitaryProof
import Langlands.Representation.Parabolic.NormalizedAdmissibilityProof
import Langlands.Representation.Unitary.AdmissibleSemisimplicityProof

/-!
# Analytic tempered induction from the actual GL block Levi

The input positive form and its preservation under normalized induction,
together with independent induced admissibility, give complete reducibility.
The published analytic preservation theorem supplies temperedness.
-/

namespace Langlands

universe uF uV

/-- An irreducible analytically tempered representation of the actual block
Levi is unitarizable, and its normalized induction is semisimple and tempered. -/
theorem glTemperedInduction :
    GLTemperedInductionStatement.{uF, uV} := by
  intro p _ F T
  let := T.topology
  dsimp only
  intro n hn B _ _ μ _ V _ _ σ hσ htemp
  let := T.generalLinearTopologicalGroup n
  have hunitary : IsUnitarizable σ :=
    glLeviTemperedUnitarity.{uF, uV} p F T n hn B μ V σ hσ htemp
  have hinduced : IsUnitarizable (T.normalizedParabolicInduced B σ) :=
    glNormalizedParabolicInductionUnitarity.{uF, uV}
      p F T n hn B V σ htemp.isAdmissible.1 hunitary
  have hadmissible : IsAdmissible (T.normalizedParabolicInduced B σ) :=
    Parabolic.normalizedInductionAdmissibility F T B V σ htemp.isAdmissible
  have hsemisimple :
      Representation.IsSemisimpleRepresentation (T.normalizedParabolicInduced B σ) :=
    admissibleUnitarySemisimplicity.{uF, max uF uV}
      (GeneralLinear n F.Carrier) (GeneralLinear.compactOpen_cofinal F T n)
      _ (T.normalizedParabolicInduced B σ) hadmissible hinduced
  have hanalytic : T.IsTempered (T.normalizedParabolicInduced B σ) :=
    glTemperedInductionPreservation.{uF, uV} p F T n hn B μ V σ hσ htemp
  exact ⟨hunitary, hsemisimple, hanalytic⟩

end Langlands
