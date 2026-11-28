import Langlands.BaseChange.TwistedCharacter.SupportSplitting
import Langlands.BaseChange.TwistedPseudoCoefficientSpanning

/-! # Splitting of the twisted irreducible spectrum at a σ-discrete orbit -/

noncomputable section

namespace Langlands.BaseChange

open GeneralLinear HarmonicAnalysis MeasureTheory PadicField.TopologicalData

universe u v z

set_option maxHeartbeats 1600000 in
/-- Transfer the p-adic separation at a compact level to the original extension field, and
combine it with spanning by the orbit, the other essentially tempered classes and proper
inductions. -/
theorem twistedPseudoCoefficientSpectrumSplitting :
    TwistedPseudoCoefficientSpectrumSplittingStatement.{u,v,z} := by
  intro F _ _ _ _ _ E _ _ _ _ _ σ l n hE hn
  let : Module.Finite F E := hE.1
  let : MeasurableSpace (GeneralLinear n E) := borel _
  let : BorelSpace (GeneralLinear n E) := ⟨rfl⟩
  let := generalLinear_t2Space_of_finite F E n
  let := generalLinear_locallyCompactSpace_of_finite F E n
  let := generalLinear_totallyDisconnectedSpace_of_finite F E n
  let := LocalField.FiniteExtension.valuativeRel F E
  let := LocalField.FiniteExtension.isLocalField_of_isModuleTopology F E
  let : CharZero E := charZero_of_injective_algebraMap (algebraMap F E).injective
  let T := CharZeroLocalField.topologicalData E
  let : Algebra F (CharZeroLocalField.padicField E).Carrier := ‹Algebra F E›
  intro W _ _ τ hτ μ _
  have hpos : 0 < n := by omega
  obtain ⟨J, hJc, hdisj⟩ :=
    @exists_compact_disjoint_twistedOrbitSpan_complement_padic.{u,v,z}
      F _ _ (CharZeroLocalField.residueChar E) _ (CharZeroLocalField.padicField E) _ T
      (inferInstanceAs (IsModuleTopology F E)) σ n hpos l hE.pos hE.pow_eq_one W _ _ τ hτ
      (inferInstanceAs (T2Space (GeneralLinear n E)))
      (inferInstanceAs (LocallyCompactSpace (GeneralLinear n E)))
      (inferInstanceAs (TotallyDisconnectedSpace (GeneralLinear n E)))
      (inferInstanceAs (MeasurableSpace (GeneralLinear n E)))
      (inferInstanceAs (BorelSpace (GeneralLinear n E))) μ
      (inferInstanceAs μ.IsHaarMeasure)
  refine ⟨J, hJc, hdisj, ?_⟩
  have hspan := twistedPseudoCoefficientSpanning.{u,v,z} F E σ l n hE hpos W τ μ
  refine hspan.trans (sup_le (sup_le le_sup_left ?_) ?_)
  · exact le_sup_of_le_right (le_sup_left.trans le_sup_left)
  · exact le_sup_of_le_right (le_sup_right.trans le_sup_left)

end Langlands.BaseChange
