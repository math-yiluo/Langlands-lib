import Langlands.Representation.Unitary.SquareIntegrableProof
import Langlands.Representation.Induction.UnitaryProof
import Langlands.Representation.Parabolic.NormalizedAdmissibilityProof
import Langlands.Representation.Unitary.AdmissibleSemisimplicityProof
import Langlands.Representation.Category.Contragredient
import Langlands.Representation.Classification.OppositeReversalSemisimple
import Langlands.Group.GL.CompactOpen
import Langlands.Group.GL.LeviCentralQuotientMeasure

/-!
# Positive forms and semisimplicity for discrete-series induction

The existing coefficient-integral construction gives an actual positive form
on a square-integrable irreducible representation of the full product Levi.
Normalized induction and admissibility then give algebraic semisimplicity.
-/

noncomputable section

namespace Langlands

universe uF uW

variable {p : ℕ} [Fact p.Prime] {F : PadicField.{uF} p}
variable (T : F.TopologicalData) {n : ℕ} (B : GeneralLinear.BlockShape n)

/-- Choose the invariant positive form supplied by the published coefficient
integral construction for the actual product Levi and given quotient measure. -/
def leviDiscreteSeriesForm :
    letI := T.topology
    letI := T.leviTopologicalGroup B
    let M := B.Levi F.Carrier
    let Q := M ⧸ Subgroup.center M
    ∀ [MeasurableSpace Q] [BorelSpace Q]
      (μ : MeasureTheory.Measure Q) [MeasureTheory.Measure.IsHaarMeasure μ]
      {W : Type uW} [AddCommGroup W] [Module ℂ W]
      (σ : Representation ℂ M W),
      Representation.IsIrreducible σ → IsSquareIntegrableModCenter σ μ →
        InvariantPositiveForm σ := by
  let := T.topology
  let := T.leviTopologicalGroup B
  let := T.leviT2Space B
  let := T.leviLocallyCompactSpace B
  have : ∀ i : Fin B.length,
      SecondCountableTopology (GeneralLinear (B.size i) F.Carrier) :=
    fun i => T.generalLinearSecondCountableTopology (B.size i)
  let : SecondCountableTopology (B.Levi F.Carrier) := inferInstance
  intro M Q _ _ μ _ W _ _ σ hσ hσsq
  let := (T.leviCentralQuotientHaar_unimodular B μ).1
  have hcofinal : ∀ H : OpenSubgroup M,
      ∃ K : OpenSubgroup M, IsCompact (K : Set M) ∧ K ≤ H := by
    intro H
    obtain ⟨K, hK, hKH⟩ := T.leviCompactOpen B H (H.isOpen.mem_nhds H.one_mem)
    exact ⟨K, hK, fun _ hx => hKH hx⟩
  exact Classical.choice
    (squareIntegrableUnimodularUnitarity.{uF, uW} M hcofinal W σ μ hσ hσsq)

/-- Upper normalized induction of any admissible unitarizable actual Levi
representation is algebraically semisimple. -/
theorem isSemisimple_normalizedParabolicInduced_of_admissible_unitarizable
    (hn : 0 < n) :
    letI := T.topology
    letI := T.leviTopologicalGroup B
    ∀ {W : Type uW} [AddCommGroup W] [Module ℂ W]
      (σ : Representation ℂ (B.Levi F.Carrier) W),
      IsAdmissible σ → IsUnitarizable σ →
        Representation.IsSemisimpleRepresentation
          (T.normalizedParabolicInduced B σ) := by
  let := T.topology
  let := T.leviTopologicalGroup B
  let := T.generalLinearTopologicalGroup n
  intro W _ _ σ hσadm hσunit
  have hunit := glNormalizedParabolicInductionUnitarity.{uF, uW}
    p F T n hn B W σ hσadm.1 hσunit
  have hadm := Parabolic.normalizedInductionAdmissibility F T B W σ hσadm
  exact admissibleUnitarySemisimplicity.{uF, max uF uW}
    (GeneralLinear n F.Carrier) (GeneralLinear.compactOpen_cofinal F T n)
    _ (T.normalizedParabolicInduced B σ) hadm hunit

/-- Both actual normalized inductions of an irreducible square-integrable
representation of the full Levi are algebraically semisimple. -/
theorem isSemisimple_bothInduced_of_squareIntegrable (hn : 0 < n) :
    letI := T.topology
    letI := T.leviTopologicalGroup B
    let M := B.Levi F.Carrier
    let Q := M ⧸ Subgroup.center M
    ∀ [MeasurableSpace Q] [BorelSpace Q]
      (μ : MeasureTheory.Measure Q) [MeasureTheory.Measure.IsHaarMeasure μ]
      {W : Type uW} [AddCommGroup W] [Module ℂ W]
      (σ : Representation ℂ M W),
      Representation.IsIrreducible σ → IsSquareIntegrableModCenter σ μ →
        Representation.IsSemisimpleRepresentation
          (T.normalizedParabolicInduced B σ) ∧
        Representation.IsSemisimpleRepresentation
          (T.normalizedOppositeParabolicInduced B σ) := by
  let := T.topology
  let := T.leviTopologicalGroup B
  let := T.generalLinearTopologicalGroup n
  intro M Q _ _ μ _ W _ _ σ hσ hσsq
  let b := leviDiscreteSeriesForm T B μ σ hσ hσsq
  have hunit : IsUnitarizable σ := ⟨b⟩
  refine ⟨isSemisimple_normalizedParabolicInduced_of_admissible_unitarizable
    T B hn σ hσsq.1 hunit, ?_⟩
  let := T.leviTopologicalGroup B.reverse
  let φ := T.leviReverse B
  let σ' := σ.comp φ.toMonoidHom
  have hadm' : IsAdmissible σ' :=
    isAdmissible_comp_continuousMulEquiv σ φ hσsq.1
  have hunit' : IsUnitarizable σ' :=
    ⟨{ b with invariant := fun g v w => b.invariant (φ g) v w }⟩
  have hss := isSemisimple_normalizedParabolicInduced_of_admissible_unitarizable
    T B.reverse hn σ' hadm' hunit'
  let E := T.oppositeReversalEquiv B σ
  rw [Representation.isSemisimpleRepresentation_iff_isSemisimpleModule_asModule] at hss ⊢
  exact ((Representation.IntertwiningMap.equivLinearMapAsModule _ _
    E.symm.toIntertwiningMap).isSemisimpleModule_iff_of_bijective E.symm.bijective).mp hss

end Langlands
