import Langlands.Representation.Unitary.CentralQuotientForm
import Langlands.Representation.Plancherel.CentralSubgroupCoefficients
import Mathlib.MeasureTheory.Group.Action

/-! # Positive forms from square-integrability modulo a central subgroup -/

noncomputable section

namespace Langlands

open MeasureTheory

universe uG uV

namespace Plancherel

variable {G : Type uG} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [T2Space G] [LocallyCompactSpace G] [SecondCountableTopology G]
  {V : Type uV} [AddCommGroup V] [Module ℂ V]
  {ρ : Representation ℂ G V}
  (C : Subgroup G) [C.Normal] (hC : C ≤ Subgroup.center G)
  [MeasurableSpace (G ⧸ C)] [BorelSpace (G ⧸ C)]
  [MeasurableSpace (G ⧸ Subgroup.center G)] [BorelSpace (G ⧸ Subgroup.center G)]

omit [T2Space G] [LocallyCompactSpace G] [SecondCountableTopology G] in
/-- Pushing forward a coefficient norm along the actual central-quotient map
preserves its square-integrability. -/
theorem centralSubgroupCoefficientNorm_memLp_map
    (c : UnitaryCentralCharacter ρ) (hρ : IsSmooth ρ)
    (ℓ : Module.Dual ℂ V) (v : V) (μ : Measure (G ⧸ C))
    (hL2 : MemLp (centralSubgroupCoefficientNorm C hC c ℓ v) 2 μ) :
    MemLp (c.coefficientNorm ℓ v) 2 (μ.map (centralQuotientProjection C hC)) := by
  exact (memLp_map_measure_iff
    (c.continuous_coefficientNorm ℓ v (hρ v)).aestronglyMeasurable
    (centralQuotientProjection C hC).continuous.measurable.aemeasurable).2 hL2

omit [T2Space G] in
/-- A square-integrable coefficient that is nonzero at the identity makes the
pushforward to the full central quotient a Haar measure. The subgroup `C` need
not be closed. -/
theorem centralQuotientProjection_map_isHaarMeasure
    (c : UnitaryCentralCharacter ρ) (hρ : IsSmooth ρ)
    (ℓ : Module.Dual ℂ V) (v : V) (hv : ℓ v ≠ 0)
    (μ : Measure (G ⧸ C)) [μ.IsHaarMeasure]
    (hL2 : MemLp (centralSubgroupCoefficientNorm C hC c ℓ v) 2 μ) :
    (μ.map (centralQuotientProjection C hC)).IsHaarMeasure := by
  let π := centralQuotientProjection C hC
  have hπ : Function.Surjective π := by
    intro q
    induction q using QuotientGroup.induction_on with
    | H g => exact ⟨QuotientGroup.mk g, rfl⟩
  let ν := μ.map π
  have : ν.IsMulLeftInvariant :=
    isMulLeftInvariant_map π.toMonoidHom.toMulHom π.continuous.measurable hπ
  have : ν.IsOpenPosMeasure := π.continuous.isOpenPosMeasure_map hπ
  have hL2' : MemLp (c.coefficientNorm ℓ v) 2 ν :=
    centralSubgroupCoefficientNorm_memLp_map C hC c hρ ℓ v μ hL2
  let f : G ⧸ Subgroup.center G → ℝ := fun q => (c.coefficientNorm ℓ v q) ^ 2
  have hf : Continuous f := (c.continuous_coefficientNorm ℓ v (hρ v)).pow 2
  have hf1 : 0 < f 1 := by
    change 0 < (‖matrixCoefficient ρ ℓ v 1‖ : ℝ) ^ 2
    simpa [matrixCoefficient] using sq_pos_of_pos (norm_pos_iff.mpr hv)
  have hfin : ν {q | f 1 / 2 < f q} < ⊤ :=
    hL2'.integrable_sq.measure_gt_lt_top (half_pos hf1)
  have : IsLocallyFiniteMeasure ν :=
    isLocallyFiniteMeasure_of_smulInvariant (G ⧸ Subgroup.center G)
      (isOpen_lt continuous_const hf) ⟨1, by dsimp; linarith⟩ hfin.ne
  exact { }

/-- The invariant positive form obtained from square-integrability modulo an
arbitrary prescribed central subgroup of a unimodular group. -/
def squareIntegrableCentralSubgroupForm
    (hcofinal : ∀ K : OpenSubgroup G, ∃ L : OpenSubgroup G,
      IsCompact (L : Set G) ∧ L ≤ K)
    (hmod : ∀ g : G, Measure.modularCharacter g = 1)
    (hirr : Representation.IsIrreducible ρ)
    (μ : Measure (G ⧸ C)) [μ.IsHaarMeasure]
    (hsq : IsSquareIntegrableModCentralSubgroup C hC ρ μ) :
    InvariantPositiveForm ρ := by
  apply Classical.choice
  obtain ⟨hadm, c, hL2⟩ := hsq
  obtain ⟨ℓ, hℓ⟩ :=
    exists_nonzero_smoothDual_of_irreducible_compact_cofinal hcofinal ρ hadm.1 hirr
  obtain ⟨v, hv⟩ : ∃ v, ℓ.1 v ≠ 0 := by
    by_contra hn
    push Not at hn
    apply hℓ
    ext v
    exact hn v
  let ν := μ.map (centralQuotientProjection C hC)
  have : ν.IsHaarMeasure :=
    centralQuotientProjection_map_isHaarMeasure C hC c hadm.1 ℓ.1 v hv μ (hL2 ℓ v)
  exact ⟨c.unimodularCoefficientProductForm hmod hadm.1 hirr ℓ.1 hℓ ν
    (fun w => centralSubgroupCoefficientNorm_memLp_map C hC c hadm.1 ℓ.1 w μ (hL2 ℓ w))⟩

end Plancherel

end Langlands
