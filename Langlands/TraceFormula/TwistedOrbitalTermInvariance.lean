import Langlands.Analysis.Local.QuotientCompatibleScaling
import Langlands.TraceFormula.TwistedGeometricConjugation
import Langlands.BaseChange.RegularTransferMeasures

/-!
# The orbital terms of the simple trace formula depend only on the class

Let `G` be a locally compact second countable Hausdorff group, `Γ` a discrete subgroup, `θ` a
continuous endomorphism of `G` and `γ ∈ G`, with twisted centralizer `C = twistedCentralizer θ γ`.
An *admissible triple* at `γ` is a right-invariant measure `μC` on `C`, finite on compacts and
positive on open sets, a quotient measure `νC` on `C \ G` compatible with `(μG, μC)`, and a quotient
measure `νΓC` on `(Γ ∩ C) \ C` compatible with `(μC, count)`. Its orbital term at `φ : G → ℂ` is
`twistedOrbitalTerm Γ θ γ νC νΓC φ = vol((Γ ∩ C) \ C) · O_γ(φ)`.

* `twistedOrbitalTerm_eq_of_isCompatible`: for fixed `γ` the volume is finite or not, the orbit
  function is integrable or not, and the term has the same value, for all admissible triples.
* `exists_isCompatible_twistedConj`: for `δ ∈ Γ` and a left-invariant `μG`, an admissible triple at
  `γ` is carried by conjugation with `δ` to an admissible triple at `δ⁻¹ γ θ(δ)` with the same
  volume, the same integrability of the orbit function and the same orbital integral.
* `exists_isCompatible_of_isTwistedConjugate`: the same for `IsTwistedConjugate Γ θ γ γ'`.
* `twistedOrbitalTerm_eq_of_isTwistedConjugate`: if `γ` and `γ'` are twisted conjugate under `Γ`,
  then for all admissible triples at `γ` and at `γ'` the volumes are finite together, the orbit
  functions are integrable together and the two orbital terms are equal.
* `orbitalTerm_eq_of_isCompatible`, `exists_isCompatible_conj`, `orbitalTerm_eq_of_isConjugate`:
  the untwisted case `θ = id`, in the form of the summands of
  `GeneralLinearSimpleTraceFormulaStatement`.

The measurable structures of the two coset spaces are instance arguments with `BorelSpace`, as in
`GeneralLinearSimpleTraceFormulaStatement`.
-/

noncomputable section

namespace Langlands.TraceFormula

open MeasureTheory MeasureTheory.Measure Topology
open Langlands.QuotientIntegration Langlands.BaseChange
open scoped NNReal ENNReal

universe u

section Term

variable {G : Type u} [Group G]

/-- The orbital term `vol((Γ ∩ C) \ C) · O_γ(φ)` of the (twisted) simple trace formula, for a
measure `νC` on `C \ G` and a measure `νΓC` on `(Γ ∩ C) \ C`, where `C = twistedCentralizer θ γ`:
`((νΓC univ).toReal : ℂ) * twistedOrbitalIntegral θ γ νC φ`. -/
def twistedOrbitalTerm (Γ : Subgroup G) (θ : G →* G) (γ : G)
    [MeasurableSpace (LeftQuotient (twistedCentralizer θ γ))]
    [MeasurableSpace (LeftQuotient (Γ.subgroupOf (twistedCentralizer θ γ)))]
    (νC : Measure (LeftQuotient (twistedCentralizer θ γ)))
    (νΓC : Measure (LeftQuotient (Γ.subgroupOf (twistedCentralizer θ γ)))) (φ : G → ℂ) : ℂ :=
  ((νΓC Set.univ).toReal : ℂ) * twistedOrbitalIntegral θ γ νC φ

end Term

section Measures

variable {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [T2Space G]
  [LocallyCompactSpace G] [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G]

omit [IsTopologicalGroup G] [T2Space G] [LocallyCompactSpace G] [SecondCountableTopology G]
  [MeasurableSpace G] [BorelSpace G] in
/-- The intersection of a discrete subgroup with a subgroup `C` is discrete in `C`. -/
theorem discreteTopology_subgroupOf (Γ : Subgroup G) [DiscreteTopology Γ] (C : Subgroup G) :
    DiscreteTopology (Γ.subgroupOf C) :=
  DiscreteTopology.of_continuous_injective
    (f := fun x : Γ.subgroupOf C => (⟨x.val.val, x.property⟩ : Γ))
    ((continuous_subtype_val.comp continuous_subtype_val).subtype_mk _)
    (fun x y h => by
      have h' := congrArg Subtype.val h
      exact Subtype.ext (Subtype.ext h'))

/-- **Independence of the measures.** Let `C` be the twisted centralizer of `γ` for a continuous
endomorphism `θ`, and `Γ` a discrete subgroup. For two admissible triples `(μC, νC, νΓC)` and
`(μC', νC', νΓC')` at `γ` there is `c : ℝ≥0`, `c ≠ 0`, with `μC' = c • μC`, `νC = c • νC'` and
`νΓC' = c • νΓC`. Hence the volumes of `(Γ ∩ C) \ C` are finite together, the orbit functions of
every `φ` are integrable together, and the orbital terms are equal. The ambient measure `μG` is
arbitrary. -/
theorem twistedOrbitalTerm_eq_of_isCompatible (Γ : Subgroup G) [DiscreteTopology Γ]
    (θ : G →* G) (hθ : Continuous θ) (γ : G)
    [MeasurableSpace (LeftQuotient (twistedCentralizer θ γ))]
    [BorelSpace (LeftQuotient (twistedCentralizer θ γ))]
    [MeasurableSpace (LeftQuotient (Γ.subgroupOf (twistedCentralizer θ γ)))]
    [BorelSpace (LeftQuotient (Γ.subgroupOf (twistedCentralizer θ γ)))]
    (μG : Measure G)
    (μC : Measure (twistedCentralizer θ γ)) [μC.IsMulRightInvariant]
    [IsFiniteMeasureOnCompacts μC] [μC.IsOpenPosMeasure]
    (μC' : Measure (twistedCentralizer θ γ)) [μC'.IsMulRightInvariant]
    [IsFiniteMeasureOnCompacts μC'] [μC'.IsOpenPosMeasure]
    {νC νC' : Measure (LeftQuotient (twistedCentralizer θ γ))}
    {νΓC νΓC' : Measure (LeftQuotient (Γ.subgroupOf (twistedCentralizer θ γ)))}
    (hνC : IsCompatible (twistedCentralizer θ γ) μG μC νC)
    (hνC' : IsCompatible (twistedCentralizer θ γ) μG μC' νC')
    (hνΓC : IsCompatible (Γ.subgroupOf (twistedCentralizer θ γ)) μC Measure.count νΓC)
    (hνΓC' : IsCompatible (Γ.subgroupOf (twistedCentralizer θ γ)) μC' Measure.count νΓC') :
    (νΓC Set.univ ≠ ⊤ ↔ νΓC' Set.univ ≠ ⊤) ∧
      (∀ φ : G → ℂ, Integrable (twistedOrbitFunction θ γ φ) νC ↔
        Integrable (twistedOrbitFunction θ γ φ) νC') ∧
      ∀ φ : G → ℂ, twistedOrbitalTerm Γ θ γ νC νΓC φ = twistedOrbitalTerm Γ θ γ νC' νΓC' φ := by
  have hC : IsClosed (twistedCentralizer θ γ : Set G) := isClosed_twistedCentralizer θ hθ γ
  have : LocallyCompactSpace (twistedCentralizer θ γ) := hC.locallyCompactSpace
  have : SecondCountableTopology (twistedCentralizer θ γ) :=
    TopologicalSpace.Subtype.secondCountableTopology (twistedCentralizer θ γ : Set G)
  have : DiscreteTopology (Γ.subgroupOf (twistedCentralizer θ γ)) :=
    discreteTopology_subgroupOf Γ (twistedCentralizer θ γ)
  have hR : IsClosed (Γ.subgroupOf (twistedCentralizer θ γ) : Set (twistedCentralizer θ γ)) :=
    Subgroup.isClosed_of_discreteTopology
  have : IsFiniteMeasureOnCompacts
      (Measure.count : Measure (Γ.subgroupOf (twistedCentralizer θ γ))) :=
    ⟨fun _ hK => Measure.count_apply_lt_top.mpr hK.finite_of_discrete⟩
  have : (Measure.count : Measure (Γ.subgroupOf (twistedCentralizer θ γ))).IsOpenPosMeasure :=
    ⟨fun _ _ hU => Measure.count_ne_zero hU⟩
  obtain ⟨c, hc0, hc⟩ := exists_eq_smul_of_isMulRightInvariant μC μC'
  have hνeq : c • νC' = νC := by
    simpa only [one_smul] using
      hνC.smul_eq_smul hC hνC' (a := 1) (b := c) (one_smul _ _).symm hc
  have hνΓeq : νΓC' = c • νΓC := by
    simpa only [one_smul] using
      hνΓC.smul_eq_smul hR hνΓC' (a := c) (b := 1) hc (one_smul _ _).symm
  have hc0' : (c : ℝ≥0∞) ≠ 0 := ENNReal.coe_ne_zero.mpr hc0
  have hvol : νΓC' Set.univ = (c : ℝ≥0∞) * νΓC Set.univ := by
    rw [hνΓeq, Measure.smul_apply, ENNReal.smul_def, smul_eq_mul]
  refine ⟨?_, fun φ => ?_, fun φ => ?_⟩
  · rw [hvol]
    exact ⟨fun h => ENNReal.mul_ne_top ENNReal.coe_ne_top h,
      fun h h' => h (by rw [h', ENNReal.mul_top hc0'])⟩
  · rw [← hνeq]
    exact integrable_smul_measure hc0' ENNReal.coe_ne_top
  · rw [twistedOrbitalTerm, twistedOrbitalTerm, ← hνeq, twistedOrbitalIntegral_smul_measure, hvol,
      ENNReal.toReal_mul, ENNReal.coe_toReal, Complex.real_smul, Complex.ofReal_mul]
    ring

end Measures

section Transport

variable {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

theorem twistedCentralizerConj_mem_subgroupOf_iff (Γ : Subgroup G) (θ : G →* G) (γ : G) {δ : G}
    (hδ : δ ∈ Γ) (y : twistedCentralizer θ γ) :
    twistedCentralizerConj θ γ δ y ∈ Γ.subgroupOf (twistedCentralizer θ (twistedConj θ δ γ)) ↔
      y ∈ Γ.subgroupOf (twistedCentralizer θ γ) := by
  change ((twistedCentralizerConj θ γ δ y : twistedCentralizer θ (twistedConj θ δ γ)) : G) ∈ Γ ↔
    (y : G) ∈ Γ
  rw [twistedCentralizerConj_apply_coe]
  constructor
  · intro h
    have e : δ * (δ⁻¹ * y.val * δ) * δ⁻¹ = y.val := by group
    exact e ▸ Γ.mul_mem (Γ.mul_mem hδ h) (Γ.inv_mem hδ)
  · intro h
    exact Γ.mul_mem (Γ.mul_mem (Γ.inv_mem hδ) h) hδ

/-- For `δ ∈ Γ`, conjugation `y ↦ δ⁻¹ y δ` maps `Γ ∩ C(γ)` onto `Γ ∩ C(δ⁻¹ γ θ(δ))`. -/
def rationalTwistedCentralizerConj (Γ : Subgroup G) (θ : G →* G) (γ : G) {δ : G}
    (hδ : δ ∈ Γ) :
    Γ.subgroupOf (twistedCentralizer θ γ) ≃ₜ*
      Γ.subgroupOf (twistedCentralizer θ (twistedConj θ δ γ)) :=
  subgroupContinuousMulEquiv (twistedCentralizerConj θ γ δ) _ _
    (twistedCentralizerConj_mem_subgroupOf_iff Γ θ γ hδ)

/-- The homeomorphism `(Γ ∩ C(γ)) \ C(γ) ≃ (Γ ∩ C(δ⁻¹ γ θ(δ))) \ C(δ⁻¹ γ θ(δ))` induced by
conjugation with `δ ∈ Γ`. -/
def rationalTwistedCentralizerQuotientConj (Γ : Subgroup G) (θ : G →* G) (γ : G) {δ : G}
    (hδ : δ ∈ Γ) :
    LeftQuotient (Γ.subgroupOf (twistedCentralizer θ γ)) ≃ₜ
      LeftQuotient (Γ.subgroupOf (twistedCentralizer θ (twistedConj θ δ γ))) :=
  Homeomorph.Quotient.congr (twistedCentralizerConj θ γ δ).toHomeomorph (by
    intro y z
    rw [QuotientGroup.rightRel_apply, QuotientGroup.rightRel_apply]
    change z * y⁻¹ ∈ Γ.subgroupOf (twistedCentralizer θ γ) ↔
      twistedCentralizerConj θ γ δ z * (twistedCentralizerConj θ γ δ y)⁻¹ ∈
        Γ.subgroupOf (twistedCentralizer θ (twistedConj θ δ γ))
    rw [← map_inv, ← map_mul]
    exact (twistedCentralizerConj_mem_subgroupOf_iff Γ θ γ hδ _).symm)

/-- A measurable equivalence carries counting measure to counting measure. -/
theorem map_count_measurableEquiv {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    (e : X ≃ᵐ Y) : Measure.map e (Measure.count : Measure X) = Measure.count := by
  ext s hs
  rw [Measure.map_apply e.measurable hs, Measure.count_apply (e.measurable hs),
    Measure.count_apply hs, Set.encard_preimage_of_bijective e.bijective]

variable [MeasurableSpace G] [BorelSpace G]

/-- **Transport along conjugation.** Let `δ ∈ Γ`, `γ' = twistedConj θ δ γ = δ⁻¹ γ θ(δ)` and `μG`
left invariant. An admissible triple `(μC, νC, νΓC)` at `γ` is carried by conjugation with `δ`
(the push-forwards by `y ↦ δ⁻¹ y δ` on `C(γ)`, by `C(γ) x ↦ C(γ') δ⁻¹ x` on `C(γ) \ G`, and by the
induced map on `(Γ ∩ C(γ)) \ C(γ)`) to an admissible triple `(μC', νC', νΓC')` at `γ'` with the
same volume, the same integrability of the orbit function of every `φ`, and the same orbital
integral. -/
theorem exists_isCompatible_twistedConj (Γ : Subgroup G) (θ : G →* G) (γ : G) {δ : G}
    (hδ : δ ∈ Γ)
    [mC : MeasurableSpace (LeftQuotient (twistedCentralizer θ γ))]
    [hmC : BorelSpace (LeftQuotient (twistedCentralizer θ γ))]
    [mR : MeasurableSpace (LeftQuotient (Γ.subgroupOf (twistedCentralizer θ γ)))]
    [hmR : BorelSpace (LeftQuotient (Γ.subgroupOf (twistedCentralizer θ γ)))]
    [mC' : MeasurableSpace (LeftQuotient (twistedCentralizer θ (twistedConj θ δ γ)))]
    [hmC' : BorelSpace (LeftQuotient (twistedCentralizer θ (twistedConj θ δ γ)))]
    [mR' : MeasurableSpace
      (LeftQuotient (Γ.subgroupOf (twistedCentralizer θ (twistedConj θ δ γ))))]
    [hmR' : BorelSpace (LeftQuotient (Γ.subgroupOf (twistedCentralizer θ (twistedConj θ δ γ))))]
    (μG : Measure G) [μG.IsMulLeftInvariant]
    (μC : Measure (twistedCentralizer θ γ)) [μC.IsMulRightInvariant]
    [IsFiniteMeasureOnCompacts μC] [μC.IsOpenPosMeasure]
    (νC : Measure (LeftQuotient (twistedCentralizer θ γ)))
    (νΓC : Measure (LeftQuotient (Γ.subgroupOf (twistedCentralizer θ γ))))
    (hνC : IsCompatible (twistedCentralizer θ γ) μG μC νC)
    (hνΓC : IsCompatible (Γ.subgroupOf (twistedCentralizer θ γ)) μC Measure.count νΓC) :
    ∃ (μC' : Measure (twistedCentralizer θ (twistedConj θ δ γ)))
      (_ : μC'.IsMulRightInvariant),
      IsFiniteMeasureOnCompacts μC' ∧ μC'.IsOpenPosMeasure ∧
      ∃ (νC' : Measure (LeftQuotient (twistedCentralizer θ (twistedConj θ δ γ))))
        (νΓC' : Measure (LeftQuotient (Γ.subgroupOf (twistedCentralizer θ (twistedConj θ δ γ))))),
        IsCompatible (twistedCentralizer θ (twistedConj θ δ γ)) μG μC' νC' ∧
        IsCompatible (Γ.subgroupOf (twistedCentralizer θ (twistedConj θ δ γ))) μC'
          Measure.count νΓC' ∧
        νΓC' Set.univ = νΓC Set.univ ∧
        ∀ φ : G → ℂ,
          (Integrable (twistedOrbitFunction θ (twistedConj θ δ γ) φ) νC' ↔
            Integrable (twistedOrbitFunction θ γ φ) νC) ∧
          twistedOrbitalIntegral θ (twistedConj θ δ γ) νC' φ = twistedOrbitalIntegral θ γ νC φ := by
  obtain rfl : mC = borel _ := hmC.measurable_eq
  obtain rfl : mR = borel _ := hmR.measurable_eq
  obtain rfl : mC' = borel _ := hmC'.measurable_eq
  obtain rfl : mR' = borel _ := hmR'.measurable_eq
  let : MeasurableSpace (LeftQuotient (twistedCentralizer θ γ)) := borel _
  let : MeasurableSpace (LeftQuotient (Γ.subgroupOf (twistedCentralizer θ γ))) := borel _
  let : MeasurableSpace (LeftQuotient (twistedCentralizer θ (twistedConj θ δ γ))) := borel _
  let : MeasurableSpace
      (LeftQuotient (Γ.subgroupOf (twistedCentralizer θ (twistedConj θ δ γ)))) := borel _
  let eC := twistedCentralizerConj θ γ δ
  let eΓ := rationalTwistedCentralizerConj Γ θ γ hδ
  let eΓQ := rationalTwistedCentralizerQuotientConj Γ θ γ hδ
  let μC' := Measure.map eC μC
  have hR' : μC'.IsMulRightInvariant := isMulRightInvariant_map eC μC
  have hFin : IsFiniteMeasureOnCompacts μC' := IsFiniteMeasureOnCompacts.map μC eC.toHomeomorph
  have hPos : μC'.IsOpenPosMeasure := eC.continuous.isOpenPosMeasure_map eC.surjective
  have hνC' : IsCompatible (twistedCentralizer θ (twistedConj θ δ γ)) μG μC'
      (Measure.map (twistedOrbitQuotientConj θ γ δ) νC) :=
    isCompatible_map_twistedConj θ γ δ μC μC' μG rfl νC hνC
  have hνΓC' : IsCompatible (Γ.subgroupOf (twistedCentralizer θ (twistedConj θ δ γ))) μC'
      Measure.count (Measure.map eΓQ νΓC) := by
    have hmap := isCompatible_map_equiv eC _ _ eΓ (fun _ => rfl) eΓQ (fun _ => rfl)
      μC Measure.count νΓC hνΓC
    have hcount : Measure.map eΓ (Measure.count :
        Measure (Γ.subgroupOf (twistedCentralizer θ γ))) = Measure.count :=
      map_count_measurableEquiv eΓ.toHomeomorph.toMeasurableEquiv
    simpa only [hcount] using hmap
  refine ⟨μC', hR', hFin, hPos, Measure.map (twistedOrbitQuotientConj θ γ δ) νC,
    Measure.map eΓQ νΓC, hνC', hνΓC', ?_, fun φ => twistedOrbitalIntegral_map_conj θ γ δ νC φ⟩
  rw [Measure.map_apply eΓQ.continuous.measurable MeasurableSet.univ, Set.preimage_univ]

/-- **Transport along a conjugacy**, the form of `exists_isCompatible_twistedConj` for
`IsTwistedConjugate Γ θ γ γ'`: an admissible triple at `γ` gives an admissible triple at `γ'` with
the same volume, the same integrability of the orbit functions and the same orbital integrals. -/
theorem exists_isCompatible_of_isTwistedConjugate (Γ : Subgroup G) (θ : G →* G) {γ γ' : G}
    (hγ : IsTwistedConjugate Γ θ γ γ')
    [MeasurableSpace (LeftQuotient (twistedCentralizer θ γ))]
    [BorelSpace (LeftQuotient (twistedCentralizer θ γ))]
    [MeasurableSpace (LeftQuotient (Γ.subgroupOf (twistedCentralizer θ γ)))]
    [BorelSpace (LeftQuotient (Γ.subgroupOf (twistedCentralizer θ γ)))]
    [MeasurableSpace (LeftQuotient (twistedCentralizer θ γ'))]
    [BorelSpace (LeftQuotient (twistedCentralizer θ γ'))]
    [MeasurableSpace (LeftQuotient (Γ.subgroupOf (twistedCentralizer θ γ')))]
    [BorelSpace (LeftQuotient (Γ.subgroupOf (twistedCentralizer θ γ')))]
    (μG : Measure G) [μG.IsMulLeftInvariant]
    (μC : Measure (twistedCentralizer θ γ)) [μC.IsMulRightInvariant]
    [IsFiniteMeasureOnCompacts μC] [μC.IsOpenPosMeasure]
    (νC : Measure (LeftQuotient (twistedCentralizer θ γ)))
    (νΓC : Measure (LeftQuotient (Γ.subgroupOf (twistedCentralizer θ γ))))
    (hνC : IsCompatible (twistedCentralizer θ γ) μG μC νC)
    (hνΓC : IsCompatible (Γ.subgroupOf (twistedCentralizer θ γ)) μC Measure.count νΓC) :
    ∃ (μC' : Measure (twistedCentralizer θ γ')) (_ : μC'.IsMulRightInvariant),
      IsFiniteMeasureOnCompacts μC' ∧ μC'.IsOpenPosMeasure ∧
      ∃ (νC' : Measure (LeftQuotient (twistedCentralizer θ γ')))
        (νΓC' : Measure (LeftQuotient (Γ.subgroupOf (twistedCentralizer θ γ')))),
        IsCompatible (twistedCentralizer θ γ') μG μC' νC' ∧
        IsCompatible (Γ.subgroupOf (twistedCentralizer θ γ')) μC' Measure.count νΓC' ∧
        νΓC' Set.univ = νΓC Set.univ ∧
        ∀ φ : G → ℂ,
          (Integrable (twistedOrbitFunction θ γ' φ) νC' ↔
            Integrable (twistedOrbitFunction θ γ φ) νC) ∧
          twistedOrbitalIntegral θ γ' νC' φ = twistedOrbitalIntegral θ γ νC φ := by
  obtain ⟨δ, hδ, hγ'⟩ := hγ
  obtain rfl : twistedConj θ δ γ = γ' := hγ'
  exact exists_isCompatible_twistedConj Γ θ γ hδ μG μC νC νΓC hνC hνΓC

/-- The untwisted case of `exists_isCompatible_twistedConj`: for `δ ∈ Γ` and a left-invariant `μG`,
an admissible triple at `γ` is carried by conjugation with `δ` to an admissible triple at
`δ⁻¹ γ δ` with the same volume, the same integrability of the orbit function and the same orbital
integral. -/
theorem exists_isCompatible_conj (Γ : Subgroup G) (γ : G) {δ : G} (hδ : δ ∈ Γ)
    [MeasurableSpace (LeftQuotient (twistedCentralizer (MonoidHom.id G) γ))]
    [BorelSpace (LeftQuotient (twistedCentralizer (MonoidHom.id G) γ))]
    [MeasurableSpace (LeftQuotient (Γ.subgroupOf (twistedCentralizer (MonoidHom.id G) γ)))]
    [BorelSpace (LeftQuotient (Γ.subgroupOf (twistedCentralizer (MonoidHom.id G) γ)))]
    [mC' : MeasurableSpace (LeftQuotient (twistedCentralizer (MonoidHom.id G) (δ⁻¹ * γ * δ)))]
    [hmC' : BorelSpace (LeftQuotient (twistedCentralizer (MonoidHom.id G) (δ⁻¹ * γ * δ)))]
    [mR' : MeasurableSpace
      (LeftQuotient (Γ.subgroupOf (twistedCentralizer (MonoidHom.id G) (δ⁻¹ * γ * δ))))]
    [hmR' : BorelSpace
      (LeftQuotient (Γ.subgroupOf (twistedCentralizer (MonoidHom.id G) (δ⁻¹ * γ * δ))))]
    (μG : Measure G) [μG.IsMulLeftInvariant]
    (μC : Measure (twistedCentralizer (MonoidHom.id G) γ)) [μC.IsMulRightInvariant]
    [IsFiniteMeasureOnCompacts μC] [μC.IsOpenPosMeasure]
    (νC : Measure (LeftQuotient (twistedCentralizer (MonoidHom.id G) γ)))
    (νΓC : Measure (LeftQuotient (Γ.subgroupOf (twistedCentralizer (MonoidHom.id G) γ))))
    (hνC : IsCompatible (twistedCentralizer (MonoidHom.id G) γ) μG μC νC)
    (hνΓC : IsCompatible (Γ.subgroupOf (twistedCentralizer (MonoidHom.id G) γ)) μC
      Measure.count νΓC) :
    ∃ (μC' : Measure (twistedCentralizer (MonoidHom.id G) (δ⁻¹ * γ * δ)))
      (_ : μC'.IsMulRightInvariant),
      IsFiniteMeasureOnCompacts μC' ∧ μC'.IsOpenPosMeasure ∧
      ∃ (νC' : Measure (LeftQuotient (twistedCentralizer (MonoidHom.id G) (δ⁻¹ * γ * δ))))
        (νΓC' : Measure
          (LeftQuotient (Γ.subgroupOf (twistedCentralizer (MonoidHom.id G) (δ⁻¹ * γ * δ))))),
        IsCompatible (twistedCentralizer (MonoidHom.id G) (δ⁻¹ * γ * δ)) μG μC' νC' ∧
        IsCompatible (Γ.subgroupOf (twistedCentralizer (MonoidHom.id G) (δ⁻¹ * γ * δ))) μC'
          Measure.count νΓC' ∧
        νΓC' Set.univ = νΓC Set.univ ∧
        ∀ φ : G → ℂ,
          (Integrable (twistedOrbitFunction (MonoidHom.id G) (δ⁻¹ * γ * δ) φ) νC' ↔
            Integrable (twistedOrbitFunction (MonoidHom.id G) γ φ) νC) ∧
          orbitalIntegral (δ⁻¹ * γ * δ) νC' φ = orbitalIntegral γ νC φ :=
  exists_isCompatible_twistedConj Γ (MonoidHom.id G) γ hδ (mC' := mC') (hmC' := hmC')
    (mR' := mR') (hmR' := hmR') μG μC νC νΓC hνC hνΓC

end Transport

section Class

variable {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [T2Space G]
  [LocallyCompactSpace G] [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G]

/-- **The orbital term of a class.** Let `γ` and `γ'` be twisted conjugate under the discrete
subgroup `Γ` (`γ' = δ⁻¹ γ θ(δ)` for some `δ ∈ Γ`), `θ` continuous and `μG` left invariant. For any
admissible triple `(μC, νC, νΓC)` at `γ` and any admissible triple `(μC', νC', νΓC')` at `γ'`, the
volumes of `(Γ ∩ C) \ C` and `(Γ ∩ C') \ C'` are finite together, the orbit functions of every `φ`
are integrable together, and the two orbital terms are equal. -/
theorem twistedOrbitalTerm_eq_of_isTwistedConjugate (Γ : Subgroup G) [DiscreteTopology Γ]
    (θ : G →* G) (hθ : Continuous θ) {γ γ' : G} (hγ : IsTwistedConjugate Γ θ γ γ')
    [MeasurableSpace (LeftQuotient (twistedCentralizer θ γ))]
    [BorelSpace (LeftQuotient (twistedCentralizer θ γ))]
    [MeasurableSpace (LeftQuotient (Γ.subgroupOf (twistedCentralizer θ γ)))]
    [BorelSpace (LeftQuotient (Γ.subgroupOf (twistedCentralizer θ γ)))]
    [MeasurableSpace (LeftQuotient (twistedCentralizer θ γ'))]
    [BorelSpace (LeftQuotient (twistedCentralizer θ γ'))]
    [MeasurableSpace (LeftQuotient (Γ.subgroupOf (twistedCentralizer θ γ')))]
    [BorelSpace (LeftQuotient (Γ.subgroupOf (twistedCentralizer θ γ')))]
    (μG : Measure G) [μG.IsMulLeftInvariant]
    (μC : Measure (twistedCentralizer θ γ)) [μC.IsMulRightInvariant]
    [IsFiniteMeasureOnCompacts μC] [μC.IsOpenPosMeasure]
    {νC : Measure (LeftQuotient (twistedCentralizer θ γ))}
    {νΓC : Measure (LeftQuotient (Γ.subgroupOf (twistedCentralizer θ γ)))}
    (hνC : IsCompatible (twistedCentralizer θ γ) μG μC νC)
    (hνΓC : IsCompatible (Γ.subgroupOf (twistedCentralizer θ γ)) μC Measure.count νΓC)
    (μC' : Measure (twistedCentralizer θ γ')) [μC'.IsMulRightInvariant]
    [IsFiniteMeasureOnCompacts μC'] [μC'.IsOpenPosMeasure]
    {νC' : Measure (LeftQuotient (twistedCentralizer θ γ'))}
    {νΓC' : Measure (LeftQuotient (Γ.subgroupOf (twistedCentralizer θ γ')))}
    (hνC' : IsCompatible (twistedCentralizer θ γ') μG μC' νC')
    (hνΓC' : IsCompatible (Γ.subgroupOf (twistedCentralizer θ γ')) μC' Measure.count νΓC') :
    (νΓC Set.univ ≠ ⊤ ↔ νΓC' Set.univ ≠ ⊤) ∧
      (∀ φ : G → ℂ, Integrable (twistedOrbitFunction θ γ φ) νC ↔
        Integrable (twistedOrbitFunction θ γ' φ) νC') ∧
      ∀ φ : G → ℂ, twistedOrbitalTerm Γ θ γ νC νΓC φ = twistedOrbitalTerm Γ θ γ' νC' νΓC' φ := by
  obtain ⟨μT, hT, hTfin, hTpos, νT, νΓT, hνT, hνΓT, hvol, hint⟩ :=
    exists_isCompatible_of_isTwistedConjugate Γ θ hγ μG μC νC νΓC hνC hνΓC
  obtain ⟨h1, h2, h3⟩ := twistedOrbitalTerm_eq_of_isCompatible Γ θ hθ γ' μG μT μC' hνT hνC'
    hνΓT hνΓC'
  refine ⟨?_, fun φ => ?_, fun φ => ?_⟩
  · rw [← hvol]
    exact h1
  · rw [← (hint φ).1]
    exact h2 φ
  · rw [← h3 φ, twistedOrbitalTerm, twistedOrbitalTerm, hvol, (hint φ).2]

/-- The untwisted case of `twistedOrbitalTerm_eq_of_isCompatible`: for fixed `γ`, the volume, the
integrability of the orbit function and the term `vol((Γ ∩ C) \ C) · O_γ(φ)` do not depend on the
admissible triple. -/
theorem orbitalTerm_eq_of_isCompatible (Γ : Subgroup G) [DiscreteTopology Γ] (γ : G)
    [MeasurableSpace (LeftQuotient (twistedCentralizer (MonoidHom.id G) γ))]
    [BorelSpace (LeftQuotient (twistedCentralizer (MonoidHom.id G) γ))]
    [MeasurableSpace (LeftQuotient (Γ.subgroupOf (twistedCentralizer (MonoidHom.id G) γ)))]
    [BorelSpace (LeftQuotient (Γ.subgroupOf (twistedCentralizer (MonoidHom.id G) γ)))]
    (μG : Measure G)
    (μC : Measure (twistedCentralizer (MonoidHom.id G) γ)) [μC.IsMulRightInvariant]
    [IsFiniteMeasureOnCompacts μC] [μC.IsOpenPosMeasure]
    (μC' : Measure (twistedCentralizer (MonoidHom.id G) γ)) [μC'.IsMulRightInvariant]
    [IsFiniteMeasureOnCompacts μC'] [μC'.IsOpenPosMeasure]
    {νC νC' : Measure (LeftQuotient (twistedCentralizer (MonoidHom.id G) γ))}
    {νΓC νΓC' : Measure (LeftQuotient (Γ.subgroupOf (twistedCentralizer (MonoidHom.id G) γ)))}
    (hνC : IsCompatible (twistedCentralizer (MonoidHom.id G) γ) μG μC νC)
    (hνC' : IsCompatible (twistedCentralizer (MonoidHom.id G) γ) μG μC' νC')
    (hνΓC : IsCompatible (Γ.subgroupOf (twistedCentralizer (MonoidHom.id G) γ)) μC
      Measure.count νΓC)
    (hνΓC' : IsCompatible (Γ.subgroupOf (twistedCentralizer (MonoidHom.id G) γ)) μC'
      Measure.count νΓC') :
    (νΓC Set.univ ≠ ⊤ ↔ νΓC' Set.univ ≠ ⊤) ∧
      (∀ φ : G → ℂ, Integrable (twistedOrbitFunction (MonoidHom.id G) γ φ) νC ↔
        Integrable (twistedOrbitFunction (MonoidHom.id G) γ φ) νC') ∧
      ∀ φ : G → ℂ, ((νΓC Set.univ).toReal : ℂ) * orbitalIntegral γ νC φ =
        ((νΓC' Set.univ).toReal : ℂ) * orbitalIntegral γ νC' φ :=
  twistedOrbitalTerm_eq_of_isCompatible Γ (MonoidHom.id G) continuous_id γ μG μC μC' hνC hνC'
    hνΓC hνΓC'

/-- The untwisted case of `twistedOrbitalTerm_eq_of_isTwistedConjugate`: if `γ' = δ⁻¹ γ δ` for some
`δ ∈ Γ`, then for any admissible triples at `γ` and at `γ'` the volumes are finite together, the
orbit functions are integrable together, and
`vol((Γ ∩ C) \ C) · O_γ(φ) = vol((Γ ∩ C') \ C') · O_γ'(φ)`. This is the form of the summands of
`GeneralLinearSimpleTraceFormulaStatement`. -/
theorem orbitalTerm_eq_of_isConjugate (Γ : Subgroup G) [DiscreteTopology Γ] {γ γ' : G}
    (hγ : IsTwistedConjugate Γ (MonoidHom.id G) γ γ')
    [MeasurableSpace (LeftQuotient (twistedCentralizer (MonoidHom.id G) γ))]
    [BorelSpace (LeftQuotient (twistedCentralizer (MonoidHom.id G) γ))]
    [MeasurableSpace (LeftQuotient (Γ.subgroupOf (twistedCentralizer (MonoidHom.id G) γ)))]
    [BorelSpace (LeftQuotient (Γ.subgroupOf (twistedCentralizer (MonoidHom.id G) γ)))]
    [MeasurableSpace (LeftQuotient (twistedCentralizer (MonoidHom.id G) γ'))]
    [BorelSpace (LeftQuotient (twistedCentralizer (MonoidHom.id G) γ'))]
    [MeasurableSpace (LeftQuotient (Γ.subgroupOf (twistedCentralizer (MonoidHom.id G) γ')))]
    [BorelSpace (LeftQuotient (Γ.subgroupOf (twistedCentralizer (MonoidHom.id G) γ')))]
    (μG : Measure G) [μG.IsMulLeftInvariant]
    (μC : Measure (twistedCentralizer (MonoidHom.id G) γ)) [μC.IsMulRightInvariant]
    [IsFiniteMeasureOnCompacts μC] [μC.IsOpenPosMeasure]
    {νC : Measure (LeftQuotient (twistedCentralizer (MonoidHom.id G) γ))}
    {νΓC : Measure (LeftQuotient (Γ.subgroupOf (twistedCentralizer (MonoidHom.id G) γ)))}
    (hνC : IsCompatible (twistedCentralizer (MonoidHom.id G) γ) μG μC νC)
    (hνΓC : IsCompatible (Γ.subgroupOf (twistedCentralizer (MonoidHom.id G) γ)) μC
      Measure.count νΓC)
    (μC' : Measure (twistedCentralizer (MonoidHom.id G) γ')) [μC'.IsMulRightInvariant]
    [IsFiniteMeasureOnCompacts μC'] [μC'.IsOpenPosMeasure]
    {νC' : Measure (LeftQuotient (twistedCentralizer (MonoidHom.id G) γ'))}
    {νΓC' : Measure (LeftQuotient (Γ.subgroupOf (twistedCentralizer (MonoidHom.id G) γ')))}
    (hνC' : IsCompatible (twistedCentralizer (MonoidHom.id G) γ') μG μC' νC')
    (hνΓC' : IsCompatible (Γ.subgroupOf (twistedCentralizer (MonoidHom.id G) γ')) μC'
      Measure.count νΓC') :
    (νΓC Set.univ ≠ ⊤ ↔ νΓC' Set.univ ≠ ⊤) ∧
      (∀ φ : G → ℂ, Integrable (twistedOrbitFunction (MonoidHom.id G) γ φ) νC ↔
        Integrable (twistedOrbitFunction (MonoidHom.id G) γ' φ) νC') ∧
      ∀ φ : G → ℂ, ((νΓC Set.univ).toReal : ℂ) * orbitalIntegral γ νC φ =
        ((νΓC' Set.univ).toReal : ℂ) * orbitalIntegral γ' νC' φ :=
  twistedOrbitalTerm_eq_of_isTwistedConjugate Γ (MonoidHom.id G) continuous_id hγ μG μC hνC hνΓC
    μC' hνC' hνΓC'

end Class

end Langlands.TraceFormula
