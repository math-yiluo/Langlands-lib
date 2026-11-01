import Langlands.Representation.RankinSelberg.TwoBlockLowerFourierGeometry
import Langlands.Analysis.Local.QuotientAutomorphismProof
import Langlands.Representation.RankinSelberg.Measures

/-! # Exact compatible-measure preservation for actual lower duality -/

noncomputable section

namespace Langlands.RankinSelberg.TwoBlockLowerFourier

open MeasureTheory MeasureTheory.Measure GeneralLinear QuotientIntegration
  TwoBlockLowerUnipotentQuotient
open scoped NNReal ENNReal

universe uR uF

/-- An involutive continuous group automorphism has Haar modulus one. -/
theorem haarModulus_eq_one_of_involutive
    {G : Type uR} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [LocallyCompactSpace G] [MeasurableSpace G] [BorelSpace G]
    (e : G ≃ₜ* G) (he : Function.Involutive e) : mulEquivHaarChar e = 1 := by
  have hee : e.trans e = ContinuousMulEquiv.refl G := by
    ext g
    exact he g
  have hsq : mulEquivHaarChar e * mulEquivHaarChar e = 1 := by
    rw [← mulEquivHaarChar_trans, hee, mulEquivHaarChar_refl]
  apply NNReal.coe_injective
  apply (pow_eq_one_iff_of_nonneg (NNReal.coe_nonneg _) (by decide : 2 ≠ 0)).mp
  simpa only [pow_two, NNReal.coe_mul, NNReal.coe_one] using
    congrArg (fun c : ℝ≥0 => (c : ℝ)) hsq

section General

variable (R : Type uR) [CommRing R] [TopologicalSpace R] [IsTopologicalRing R]
  [T2Space R] (t : ℕ)
variable [LocallyCompactSpace (GeneralLinear (t + 1) R)]
variable [MeasurableSpace (GeneralLinear (t + 1) R)]
  [BorelSpace (GeneralLinear (t + 1) R)]
variable [MeasurableSpace (upperUnipotent (t + 1) R)]
  [BorelSpace (upperUnipotent (t + 1) R)]
variable [MeasurableSpace (LeftQuotient (upperUnipotent (t + 1) R))]
  [BorelSpace (LeftQuotient (upperUnipotent (t + 1) R))]
variable (μG : Measure (GeneralLinear (t + 1) R))
  (μN : Measure (upperUnipotent (t + 1) R))
  [IsHaarMeasure μG] [μG.Regular] [IsHaarMeasure μN] [μN.Regular]
  [IsMulRightInvariant μN]

/-- Every supplied compatible standard quotient measure is preserved exactly. -/
theorem standardDuality_preserves
    (ν : Measure (LeftQuotient (upperUnipotent (t + 1) R)))
    (hν : IsCompatible (upperUnipotent (t + 1) R) μG μN ν) :
    MeasurePreserving (standardDuality R t) ν ν := by
  have hclosed := UpperUnipotent.isClosed (R := R) (n := t + 1)
  have : LocallyCompactSpace (upperUnipotent (t + 1) R) := hclosed.locallyCompactSpace
  have hN : Function.Involutive
      (subgroupAutomorphism (upperUnipotent (t + 1) R)
        (reflectedGroup R t) (reflectedGroup_mem R t)) := by
    intro n
    apply Subtype.ext
    change reflectedGroup R t (reflectedGroup R t n.val) = n.val
    exact reflectedGroup_involutive R t n.val
  have hmap := hν.map_quotientAutomorphism (upperUnipotent (t + 1) R)
    hclosed (reflectedGroup R t) (reflectedGroup_mem R t)
  rw [haarModulus_eq_one_of_involutive _ hN,
    haarModulus_eq_one_of_involutive _ (reflectedGroup_involutive R t),
    div_self one_ne_zero, ENNReal.coe_one, one_smul] at hmap
  exact (hν.right_invariant (weylLong (t + 1) R)).comp
    ⟨(quotientAutomorphism _ _ _).continuous.measurable, hmap⟩

variable {t} {m : Fin 2 → ℕ} (h : ∑ i, (m i + 1) = t + 1)
variable [MeasurableSpace (LowerQuotient h R)] [BorelSpace (LowerQuotient h R)]
variable [MeasurableSpace (LowerQuotient (reverse_sum h) R)]
  [BorelSpace (LowerQuotient (reverse_sum h) R)]

/-- The supplied standard measure transported to the actual lower quotient. -/
def lowerQuotientMeasure
    (ν : Measure (LeftQuotient (upperUnipotent (t + 1) R))) :
    Measure (LowerQuotient h R) :=
  Measure.map (lowerToStandard h R).symm ν

/-- The single geometric duality preserves the two transported lower measures. -/
theorem lowerDuality_preserves
    (ν : Measure (LeftQuotient (upperUnipotent (t + 1) R)))
    (hν : IsCompatible (upperUnipotent (t + 1) R) μG μN ν) :
    MeasurePreserving (lowerDuality R h)
      (lowerQuotientMeasure R h ν) (lowerQuotientMeasure R (reverse_sum h) ν) := by
  have hA := MeasurableEquiv.measurePreserving_symm ν
    (lowerToStandardHomeomorph h R).symm.toMeasurableEquiv
  have hS := standardDuality_preserves R t μG μN ν hν
  have hB := (lowerToStandardHomeomorph (reverse_sum h) R).symm.continuous.measurable
    |>.measurePreserving ν
  exact hB.comp (hS.comp hA)

/-- The inverse lower duality preserves the measures in the reverse direction. -/
theorem lowerDuality_symm_preserves
    (ν : Measure (LeftQuotient (upperUnipotent (t + 1) R)))
    (hν : IsCompatible (upperUnipotent (t + 1) R) μG μN ν) :
    MeasurePreserving (lowerDuality R h).symm
      (lowerQuotientMeasure R (reverse_sum h) ν) (lowerQuotientMeasure R h ν) :=
  MeasurePreserving.symm (lowerDuality R h).toMeasurableEquiv
    (lowerDuality_preserves R μG μN h ν hν)

end General

section Padic

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p)
variable {t : ℕ} {m : Fin 2 → ℕ} (h : ∑ i, (m i + 1) = t + 1)

/-- The exact two measure laws and their restrictions, for every compatible input. -/
theorem lowerDuality_measure_transport :
    let T := F.canonicalTopologicalData
    letI := T.topology
    letI := T.valuativeRel
    letI := T.localField
    letI := T.fieldT2
    letI := T.generalLinearTopologicalGroup (t + 1)
    let G := GeneralLinear (t + 1) F.Carrier
    let N := upperUnipotent (t + 1) F.Carrier
    let Q := LeftQuotient N
    let HQ := LowerQuotient h F.Carrier
    let HQD := LowerQuotient (reverse_sum h) F.Carrier
    letI : MeasurableSpace G := borel G
    letI : BorelSpace G := ⟨rfl⟩
    letI : MeasurableSpace N := borel N
    letI : BorelSpace N := ⟨rfl⟩
    letI : MeasurableSpace Q := borel Q
    letI : BorelSpace Q := ⟨rfl⟩
    letI : MeasurableSpace HQ := borel HQ
    letI : BorelSpace HQ := ⟨rfl⟩
    letI : MeasurableSpace HQD := borel HQD
    letI : BorelSpace HQD := ⟨rfl⟩
    ∀ hN : IsMulRightInvariant (unipotentHaar F.Carrier t),
      letI := hN
      ∀ ν : Measure Q, IsCompatible N (generalLinearHaar F.Carrier t)
          (unipotentHaar F.Carrier t) ν →
        let νL := lowerQuotientMeasure F.Carrier h ν
        let νD := lowerQuotientMeasure F.Carrier (reverse_sum h) ν
        MeasurePreserving (lowerDuality F.Carrier h) νL νD ∧
        MeasurePreserving (lowerDuality F.Carrier h).symm νD νL ∧
        ∀ k : ℤ,
          Measure.map (lowerDuality F.Carrier h)
              (νL.restrict (TwoBlockLowerUnipotentQuotient.determinantSlice F h k)) =
            νD.restrict (TwoBlockLowerUnipotentQuotient.determinantSlice F (reverse_sum h) (-k)) ∧
          Measure.map (lowerDuality F.Carrier h).symm
              (νD.restrict (TwoBlockLowerUnipotentQuotient.determinantSlice F (reverse_sum h) (-k))) =
            νL.restrict (TwoBlockLowerUnipotentQuotient.determinantSlice F h k) := by
  intro T
  let := T.topology
  let := T.valuativeRel
  let := T.localField
  let := T.fieldT2
  let := T.generalLinearTopologicalGroup (t + 1)
  intro G N Q HQ HQD
  let : MeasurableSpace G := borel G
  let : BorelSpace G := ⟨rfl⟩
  let : MeasurableSpace N := borel N
  let : BorelSpace N := ⟨rfl⟩
  let : MeasurableSpace Q := borel Q
  let : BorelSpace Q := ⟨rfl⟩
  let : MeasurableSpace HQ := borel HQ
  let : BorelSpace HQ := ⟨rfl⟩
  let : MeasurableSpace HQD := borel HQD
  let : BorelSpace HQD := ⟨rfl⟩
  intro hN
  let := hN
  intro ν hν νL νD
  have : LocallyCompactSpace G := T.generalLinearLocallyCompactSpace (t + 1)
  have hD := lowerDuality_preserves F.Carrier
    (generalLinearHaar F.Carrier t) (unipotentHaar F.Carrier t) h ν hν
  have hDs := lowerDuality_symm_preserves F.Carrier
    (generalLinearHaar F.Carrier t) (unipotentHaar F.Carrier t) h ν hν
  refine ⟨hD, hDs, fun k => ?_⟩
  have hs := lowerDuality_slices F h k
  refine ⟨?_, ?_⟩
  · have hm := (hD.restrict_preimage_emb
      (lowerDuality F.Carrier h).toMeasurableEquiv.measurableEmbedding
      (TwoBlockLowerUnipotentQuotient.determinantSlice F (reverse_sum h) (-k))).map_eq
    rwa [hs.2.1] at hm
  · have hm := (hDs.restrict_preimage_emb
      (lowerDuality F.Carrier h).symm.toMeasurableEquiv.measurableEmbedding
      (TwoBlockLowerUnipotentQuotient.determinantSlice F h k)).map_eq
    rwa [hs.2.2.2] at hm

end Padic

end Langlands.RankinSelberg.TwoBlockLowerFourier
