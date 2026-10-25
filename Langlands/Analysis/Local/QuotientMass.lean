import Langlands.Analysis.Local.QuotientTopology

/-!
# Positive finite mass in actual left quotients

A compatible quotient measure is positive on every nonempty open set.
Regularity then gives positive finite mass to every nonempty compact open set.
No numerical orbit-volume formula is required.
-/

noncomputable section

namespace Langlands.QuotientIntegration

open MeasureTheory MeasureTheory.Measure

universe uG

variable {G : Type uG} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

/-- The image of an open subgroup in the actual left quotient. Compactness
of the subgroup is a separate hypothesis in the mass results. -/
def compactOpenQuotientOrbit (H : Subgroup G) (J : OpenSubgroup G) :
    Set (LeftQuotient H) :=
  leftQuotientMap H '' (J : Set G)

theorem isOpen_compactOpenQuotientOrbit (H : Subgroup G) (J : OpenSubgroup G) :
    IsOpen (compactOpenQuotientOrbit H J) :=
  (leftQuotient_isOpenQuotientMap H).isOpenMap _ J.isOpen

theorem isCompact_compactOpenQuotientOrbit (H : Subgroup G) (J : OpenSubgroup G)
    (hJ : IsCompact (J : Set G)) :
    IsCompact (compactOpenQuotientOrbit H J) :=
  hJ.image (leftQuotient_isOpenQuotientMap H).continuous

omit [IsTopologicalGroup G] in
theorem compactOpenQuotientOrbit_nonempty (H : Subgroup G) (J : OpenSubgroup G) :
    (compactOpenQuotientOrbit H J).Nonempty :=
  ⟨leftQuotientMap H 1, 1, J.one_mem, rfl⟩

variable [MeasurableSpace G] {H : Subgroup G}
variable [MeasurableSpace H] [MeasurableMul H]
variable {μG : Measure G} {μH : Measure H} [IsMulRightInvariant μH]
variable [MeasurableSpace (LeftQuotient H)] [BorelSpace (LeftQuotient H)]
variable {μ : Measure (LeftQuotient H)}

/-- Full support follows from the nonzero regularity and right-invariance
fields of compatibility. It does not require the Weil integral formula. -/
theorem IsCompatible.isOpenPosMeasure (hμ : IsCompatible H μG μH μ) :
    μ.IsOpenPosMeasure := by
  classical
  let : μ.Regular := hμ.regular
  obtain ⟨K, hK, hμK⟩ := Measure.Regular.exists_isCompact_not_null.mpr hμ.nonzero
  refine ⟨fun U hU hne => ?_⟩
  rcases hne with ⟨q, hq⟩
  obtain ⟨u, rfl⟩ := Quotient.exists_rep q
  have hcover : K ⊆ ⋃ g : G, rightTranslate H g ⁻¹' U := by
    intro x _
    induction x using Quotient.inductionOn with
    | h x =>
      apply Set.mem_iUnion.mpr
      refine ⟨x⁻¹ * u, ?_⟩
      simpa only [Set.mem_preimage, rightTranslate_mk, mul_inv_cancel_left] using hq
  obtain ⟨t, ht⟩ := hK.elim_finite_subcover
    (fun g : G => rightTranslate H g ⁻¹' U)
    (fun g => hU.preimage (rightTranslate H g).continuous) hcover
  intro hzero
  apply hμK
  apply measure_mono_null ht
  apply (measure_biUnion_null_iff t.countable_toSet).mpr
  intro g _
  exact ((hμ.right_invariant g).measure_preimage
    hU.measurableSet.nullMeasurableSet).trans hzero

/-- Every nonempty compact open subset of an actual compatible quotient has
positive finite mass, for the supplied measure itself. -/
theorem IsCompatible.measure_pos_lt_top (hμ : IsCompatible H μG μH μ)
    {C : Set (LeftQuotient H)} (hCc : IsCompact C) (hCo : IsOpen C)
    (hne : C.Nonempty) :
    0 < μ C ∧ μ C < ⊤ := by
  let : μ.Regular := hμ.regular
  let : μ.IsOpenPosMeasure := hμ.isOpenPosMeasure
  exact ⟨hCo.measure_pos μ hne, hCc.measure_lt_top⟩

/-- The open subgroup orbit of the identity coset has positive finite mass
whenever the subgroup is compact. The subgroup need not normalize `H`. -/
theorem IsCompatible.compactOpenQuotientOrbit_mass
    (hμ : IsCompatible H μG μH μ) (J : OpenSubgroup G)
    (hJ : IsCompact (J : Set G)) :
    0 < μ (compactOpenQuotientOrbit H J) ∧
      μ (compactOpenQuotientOrbit H J) < ⊤ :=
  hμ.measure_pos_lt_top (isCompact_compactOpenQuotientOrbit H J hJ)
    (isOpen_compactOpenQuotientOrbit H J) (compactOpenQuotientOrbit_nonempty H J)

end Langlands.QuotientIntegration
