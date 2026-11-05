import Langlands.Representation.Plancherel.ProductInducedOrbitForm
import Langlands.Representation.Plancherel.ProductInducedOrbitCoordinates

/-! # Integer lattice coordinate independence of actual orbit forms -/

noncomputable section

set_option maxHeartbeats 800000
set_option maxRecDepth 4096

open CategoryTheory MeasureTheory
open scoped NNReal ENNReal

namespace Langlands.Plancherel

open Aubert.General HarishChandraSchwartz Induction CompactInduction

universe uG uI uV uJ uJ' uL

variable {G : Type uG} [Group G] [TopologicalSpace G] [NonarchimedeanGroup G]
  {M : Subgroup G} {I : Type uI} (ν : I → (M →* ℝ≥0ˣ))
  {J : Type uJ} {J' : Type uJ'} [Fintype J] [Fintype J']
  (e : unitaryUnramifiedCharacters ν ≃* (J → Circle))
  {L : Type uL} [AddCommGroup L] [Module ℤ L]
  (b : Module.Basis J ℤ L) (c : Module.Basis J' ℤ L)

omit [NonarchimedeanGroup G] in
/-- Integer lattice rebasing preserves continuity of the supplied forward
character coordinates. No inverse-continuity premise is added. -/
theorem continuous_rebaseUnitaryTorusCoordinates (he : Continuous e) :
    Continuous (rebaseUnitaryTorusCoordinates ν e b c) :=
  (continuous_finiteTorusBasisChange b c).comp he

section ParameterMeasure

variable (π : IrreducibleAdmissibleRep.{0, uG, uV} (k := ℂ) (G := M))
  (C : Subgroup M) [C.Normal] (hC : C ≤ Subgroup.center M)
  [MeasurableSpace (M ⧸ C)]
  (μ : Measure (M ⧸ C)) [μ.IsHaarMeasure]
  (hsq : IsSquareIntegrableModCentralSubgroup C hC π.obj.representation μ)

/-- The coordinate pushforward retains the supplied character measure and
the inverse cardinality of the same actual stabilizer. -/
theorem map_finiteTorusBasisChange_unitaryOrbitParameterMeasure (he : Continuous e)
    (η : Measure (unitaryUnramifiedCharacters ν)) :
    Measure.map (finiteTorusBasisChange b c)
        (unitaryOrbitParameterMeasure π C hC μ hsq ν e η) =
      unitaryOrbitParameterMeasure π C hC μ hsq ν
        (rebaseUnitaryTorusCoordinates ν e b c) η := by
  rw [unitaryOrbitParameterMeasure, unitaryOrbitParameterMeasure,
    Measure.map_smul _ (continuous_finiteTorusBasisChange b c).measurable.aemeasurable,
    Measure.map_map (continuous_finiteTorusBasisChange b c).measurable he.measurable]
  rfl

end ParameterMeasure

variable [LocallyCompactSpace G] [SecondCountableTopology G]
  [MeasurableSpace G] [BorelSpace G]
  {P U : Subgroup G} [LocallyCompactSpace P]
  (h : IsSemidirectDecomposition P M U) (hU : IsClosed (U : Set G))
  (hP : IsClosed (P : Set G))
  (K : OpenSubgroup G) (hK : IsCompact (K : Set G))
  (hPK : ∀ g : G, ∃ p : P, ∃ k : K, g = (p : G) * (k : G))
  (hG : ∀ g : G, Measure.modularCharacter g = 1)
  (hδ : ∀ p : P, Measure.modularCharacter p =
    (HaarModulus.closedRestrictCharacter U hU P h.le_normalizer p : ℝ≥0))
  (π : IrreducibleAdmissibleRep.{0, uG, uV} (k := ℂ) (G := M))
  (hcof : CompactOpenCofinal M)
  (C : Subgroup M) [C.Normal] (hC : C ≤ Subgroup.center M)
  [MeasurableSpace (M ⧸ C)] [BorelSpace (M ⧸ C)]
  (μ : Measure (M ⧸ C)) [μ.IsHaarMeasure] [μ.IsInvInvariant]
  (hsq : IsSquareIntegrableModCentralSubgroup C hC π.obj.representation μ)
  (hν : ∀ i, Continuous (ν i)) (hr : Continuous h.projection)

/-- The coordinate equivalence preserves the canonical scalar pairing at
each actual discrete-series class, since every actual fiber value is fixed. -/
theorem unitaryOrbitProductPairing_rebase
    (q r : productInducedSmoothOrbitSections ν π (rebaseUnitaryTorusCoordinates ν e b c)
      h hU K hP hK hν hr hPK)
    (ω : discreteSeriesOrbit C hC μ ν (discreteSeriesClass C hC μ π hsq)) :
    unitaryOrbitProductPairing h hU hP K hK hPK hG hδ π hcof C hC μ hsq ν hν hr e
        (productInducedSmoothOrbitRebaseEquiv ν π e b c h hU K hP hK hν hr hPK q)
        (productInducedSmoothOrbitRebaseEquiv ν π e b c h hU K hP hK hν hr hPK r) ω =
      unitaryOrbitProductPairing h hU hP K hK hPK hG hδ π hcof C hC μ hsq ν hν hr
        (rebaseUnitaryTorusCoordinates ν e b c) q r ω := rfl

variable [Finite (M ⧸ (commonNormKernel ν ⊔ C))]

local instance coordinateComparisonStabilizerFinite :
    Finite (discreteSeriesStabilizer C hC μ ν (discreteSeriesClass C hC μ π hsq)) :=
  finite_discreteSeriesStabilizer ν C hC μ (discreteSeriesClass C hC μ π hsq)

/-- Rebasing preserves the actual orbit integral with its original measure.
This equality itself needs neither coordinate continuity nor finite mass. -/
theorem integral_unitaryOrbitProductPairing_rebase
    (η : Measure (unitaryUnramifiedCharacters ν))
    (q r : productInducedSmoothOrbitSections ν π (rebaseUnitaryTorusCoordinates ν e b c)
      h hU K hP hK hν hr hPK) :
    (∫ ω, unitaryOrbitProductPairing h hU hP K hK hPK hG hδ π hcof C hC μ hsq
        ν hν hr e
        (productInducedSmoothOrbitRebaseEquiv ν π e b c h hU K hP hK hν hr hPK q)
        (productInducedSmoothOrbitRebaseEquiv ν π e b c h hU K hP hK hν hr hPK r) ω
      ∂discreteSeriesOrbitMeasure ν C hC μ (discreteSeriesClass C hC μ π hsq) η) =
      ∫ ω, unitaryOrbitProductPairing h hU hP K hK hPK hG hδ π hcof C hC μ hsq
        ν hν hr (rebaseUnitaryTorusCoordinates ν e b c) q r ω
        ∂discreteSeriesOrbitMeasure ν C hC μ (discreteSeriesClass C hC μ π hsq) η := by
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun ω =>
    unitaryOrbitProductPairing_rebase
      ν e b c h hU hP K hK hPK hG hδ π hcof C hC μ hsq hν hr q r ω

/-- The existing identity on actual sections preserves the entire positive
orbit-integral core under finite integer lattice coordinate changes. -/
theorem productInducedSmoothOrbitRebaseEquiv_inner (he : Continuous e)
    (η : Measure (unitaryUnramifiedCharacters ν))
    [IsFiniteMeasure η] [η.IsOpenPosMeasure]
    (q r : productInducedSmoothOrbitSections ν π (rebaseUnitaryTorusCoordinates ν e b c)
      h hU K hP hK hν hr hPK) :
    (productInducedSmoothOrbitCore h hU hP K hK hPK hG hδ π hcof C hC μ hsq
        ν hν hr e he η).inner
        (productInducedSmoothOrbitRebaseEquiv ν π e b c h hU K hP hK hν hr hPK q)
        (productInducedSmoothOrbitRebaseEquiv ν π e b c h hU K hP hK hν hr hPK r) =
      (productInducedSmoothOrbitCore h hU hP K hK hPK hG hδ π hcof C hC μ hsq
        ν hν hr (rebaseUnitaryTorusCoordinates ν e b c)
        (continuous_rebaseUnitaryTorusCoordinates ν e b c he) η).inner q r := by
  rw [productInducedSmoothOrbitCore_inner_integral,
    productInducedSmoothOrbitCore_inner_integral]
  exact integral_unitaryOrbitProductPairing_rebase
    ν e b c h hU hP K hK hPK hG hδ π hcof C hC μ hsq hν hr η q r

/-- The coordinate comparison is a linear isometric equivalence for the
norms constructed from the actual orbit-integral cores. -/
def productInducedSmoothOrbitRebaseIsometry (he : Continuous e)
    (η : Measure (unitaryUnramifiedCharacters ν))
    [IsFiniteMeasure η] [η.IsOpenPosMeasure] :
    letI := (productInducedSmoothOrbitCore h hU hP K hK hPK hG hδ π hcof C hC μ hsq
      ν hν hr e he η).toNormedAddCommGroup
    letI := (productInducedSmoothOrbitCore h hU hP K hK hPK hG hδ π hcof C hC μ hsq
      ν hν hr (rebaseUnitaryTorusCoordinates ν e b c)
      (continuous_rebaseUnitaryTorusCoordinates ν e b c he) η).toNormedAddCommGroup
    productInducedSmoothOrbitSections ν π (rebaseUnitaryTorusCoordinates ν e b c)
        h hU K hP hK hν hr hPK ≃ₗᵢ[ℂ]
      productInducedSmoothOrbitSections ν π e h hU K hP hK hν hr hPK := by
  letI := (productInducedSmoothOrbitCore h hU hP K hK hPK hG hδ π hcof C hC μ hsq
    ν hν hr e he η).toNormedAddCommGroup
  letI := (productInducedSmoothOrbitCore h hU hP K hK hPK hG hδ π hcof C hC μ hsq
    ν hν hr (rebaseUnitaryTorusCoordinates ν e b c)
    (continuous_rebaseUnitaryTorusCoordinates ν e b c he) η).toNormedAddCommGroup
  refine { productInducedSmoothOrbitRebaseEquiv
    ν π e b c h hU K hP hK hν hr hPK with norm_map' := ?_ }
  intro q
  change Real.sqrt (Complex.re
      ((productInducedSmoothOrbitCore h hU hP K hK hPK hG hδ π hcof C hC μ hsq
        ν hν hr e he η).inner
        (productInducedSmoothOrbitRebaseEquiv ν π e b c h hU K hP hK hν hr hPK q)
        (productInducedSmoothOrbitRebaseEquiv ν π e b c h hU K hP hK hν hr hPK q))) =
    Real.sqrt (Complex.re
      ((productInducedSmoothOrbitCore h hU hP K hK hPK hG hδ π hcof C hC μ hsq
        ν hν hr (rebaseUnitaryTorusCoordinates ν e b c)
        (continuous_rebaseUnitaryTorusCoordinates ν e b c he) η).inner q q))
  rw [productInducedSmoothOrbitRebaseEquiv_inner]

@[simp]
theorem productInducedSmoothOrbitRebaseIsometry_apply (he : Continuous e)
    (η : Measure (unitaryUnramifiedCharacters ν))
    [IsFiniteMeasure η] [η.IsOpenPosMeasure]
    (q : productInducedSmoothOrbitSections ν π (rebaseUnitaryTorusCoordinates ν e b c)
      h hU K hP hK hν hr hPK) (A : UnitaryOrbitRepresentative ν π) :
    (productInducedSmoothOrbitRebaseIsometry
      ν e b c h hU hP K hK hPK hG hδ π hcof C hC μ hsq hν hr he η q).val A =
      q.val A := rfl

end Langlands.Plancherel
