import Langlands.Representation.Aubert.General.NaturalIntegralDuality
import Langlands.Representation.Aubert.General.RationalInductionDualityAssembly
import Langlands.Representation.Induction.CompactQuotientSmoothDuality

/-!
# Natural integral duality of normalized induction from a compact quotient

For an actual semidirect decomposition `P = M ⋉ U` with `P` closed and `P \ G`
compact, normalized induction commutes with the smooth contragredient on all
smooth objects, through the integral of the coefficient pairing. The Levi
inclusion `M → P` is the section required by
`Induction.exists_integralDualEquiv_of_section`, so no admissibility is needed.

* `isIntegralDuality_of_compactSpace`: `IsIntegralDuality` for any measure on
  `K` positive near `1` satisfying the scalar hypothesis for `δ = χ²`.
* `exists_isNaturalIntegralDuality_of_compactSpace`: for a unimodular group whose
  modular character on `P` is the restricted Haar modulus of conjugation on `U`,
  a measure on `G` and a natural isomorphism `i.op ⋙ D ≅ D ⋙ i` characterized by
  the integral.
-/

noncomputable section

open CategoryTheory MeasureTheory
open scoped NNReal

namespace Langlands.Aubert.General

universe uG uV

variable {G : Type uG} [Group G] [TopologicalSpace G] [LocallyCompactSpace G]
  [NonarchimedeanGroup G]
variable {P M U : Subgroup G} (h : IsSemidirectDecomposition P M U)

/-- For a closed `P` with compact `P \ G`, a measure on `K` positive on open
neighbourhoods of `1`, whose integral is right invariant on functions covariant
for `δ = χ²` (`χ` the half character), gives integral-characterized dualities
`(i A)~ ≅ i(A~)` for every smooth `A`. -/
theorem isIntegralDuality_of_compactSpace (hU : IsClosed (U : Set G))
    (hP : IsClosed (P : Set G)) (hm : Continuous h.projection)
    [CompactSpace (Induction.LeftQuotient P)] (δ : P → ℝ≥0)
    (hδ : ∀ q : P, ((HaarModulus.closedHalfCharacter U hU P h.le_normalizer q : ℂˣ) : ℂ) *
        HaarModulus.closedHalfCharacter U hU P h.le_normalizer q = ((δ q : ℝ) : ℂ))
    (K : Subgroup G) [MeasurableSpace K] (μ : Measure K)
    (hpos : ∀ W : Set K, IsOpen W → (1 : K) ∈ W → 0 < μ W)
    (hscalar : ∀ φ : G → ℂ, IsLocallyConstant φ →
      (∀ (q : P) (x : G), φ ((q : G) * x) = ((δ q : ℝ) : ℂ) * φ x) →
      ∀ g : G, Integrable (fun k : K => φ ((k : G) * g)) μ ∧
        (∫ k : K, φ ((k : G) * g) ∂μ) = ∫ k : K, φ (k : G) ∂μ) :
    IsIntegralDuality.{uG, uV} h hU K μ := by
  apply isIntegralDuality_of_twistEquiv h hU K μ
  intro A
  exact Induction.exists_integralDualEquiv_of_section P h.projection
    (HaarModulus.closedHalfCharacter U hU P h.le_normalizer) δ K μ hm
    (HaarModulus.isOpen_ker_closedHalfCharacter U hU P h.le_normalizer) hδ hpos hscalar hP
    (Subgroup.inclusion h.levi_le) (continuous_inclusion h.levi_le)
    (fun n => h.projection_levi n) A.representation A.isSmooth

/-- For a unimodular group with `P` closed and `P \ G` compact, if the modular
character of `P` is the restricted Haar modulus of conjugation on `U`, then there
are a measure on `G` and a natural isomorphism `i.op ⋙ D ≅ D ⋙ i` on all smooth
objects characterized by the integral of the coefficient pairing. -/
theorem exists_isNaturalIntegralDuality_of_compactSpace [T2Space G] [MeasurableSpace G]
    [BorelSpace G] (hU : IsClosed (U : Set G)) (hP : IsClosed (P : Set G))
    (hm : Continuous h.projection) [CompactSpace (Induction.LeftQuotient P)]
    [LocallyCompactSpace P] (hG : ∀ g : G, Measure.modularCharacter g = 1)
    (hδ : ∀ q : P, Measure.modularCharacter q =
      (HaarModulus.closedRestrictCharacter U hU P h.le_normalizer q : ℝ≥0)) :
    ∃ μ : Measure (⊤ : Subgroup G),
      ∃ C, IsNaturalIntegralDuality.{uG, uV} h hU ⊤ μ C := by
  obtain ⟨μ, hpos, hscalar⟩ := Induction.exists_compactQuotient_measure hG P hP
  have hsq : ∀ q : P,
      ((HaarModulus.closedHalfCharacter U hU P h.le_normalizer q : ℂˣ) : ℂ) *
        HaarModulus.closedHalfCharacter U hU P h.le_normalizer q =
      (((Measure.modularCharacter q : ℝ≥0) : ℝ) : ℂ) := by
    intro q
    rw [closedHalfCharacter_mul_self h hU q, hδ q]
  exact ⟨μ, exists_isNaturalIntegralDuality h hU ⊤ μ
    (isIntegralDuality_of_compactSpace h hU hP hm (fun q => Measure.modularCharacter q) hsq
      ⊤ μ hpos hscalar)⟩

end Langlands.Aubert.General
