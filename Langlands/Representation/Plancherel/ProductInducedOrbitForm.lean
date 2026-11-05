import Langlands.Representation.Plancherel.ProductInducedSmoothFamilyForm
import Langlands.Representation.Plancherel.CompactProductFormTransport
import Langlands.Representation.Plancherel.ProductInducedDiscreteSeriesOrbit
import Langlands.Representation.Plancherel.DiscreteSeriesOrbitMeasure

/-!
# Canonical scalar pairings on actual discrete-series orbits

The canonical inverse-degree forms commute with every inducing equivalence.
Coherent sections therefore have a scalar pairing on the actual class orbit.
-/

noncomputable section

set_option maxHeartbeats 800000
set_option maxRecDepth 4096

open CategoryTheory MeasureTheory
open scoped NNReal ENNReal TensorProduct

namespace Langlands.Plancherel

open Aubert.General HarishChandraSchwartz Induction CompactInduction

universe uG uI uV uJ

variable {G : Type uG} [Group G] [TopologicalSpace G] [LocallyCompactSpace G]
  [NonarchimedeanGroup G] [SecondCountableTopology G]
  [MeasurableSpace G] [BorelSpace G]
  {P M U : Subgroup G} [LocallyCompactSpace P]
  (h : IsSemidirectDecomposition P M U) (hU : IsClosed (U : Set G))
  (hP : IsClosed (P : Set G))
  (K : OpenSubgroup G) (hK : IsCompact (K : Set G))
  (hPK : ∀ g : G, ∃ p : P, ∃ k : K, g = (p : G) * (k : G))

include hPK in
omit [LocallyCompactSpace G] [NonarchimedeanGroup G]
  [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G]
  [LocallyCompactSpace P] in
private theorem compactFactorization (g : G) :
    ∃ p ∈ P, ∃ k ∈ K, g = p * k := by
  obtain ⟨p, k, hg⟩ := hPK g
  exact ⟨p, p.property, k, k.property, hg⟩

variable
  (hG : ∀ g : G, Measure.modularCharacter g = 1)
  (hδ : ∀ p : P, Measure.modularCharacter p =
    (HaarModulus.closedRestrictCharacter U hU P h.le_normalizer p : ℝ≥0))
  (π : IrreducibleAdmissibleRep.{0, uG, uV} (k := ℂ) (G := M))
  (hcof : CompactOpenCofinal M)
  (C : Subgroup M) [C.Normal] (hC : C ≤ Subgroup.center M)
  [MeasurableSpace (M ⧸ C)] [BorelSpace (M ⧸ C)]
  (μ : Measure (M ⧸ C)) [μ.IsHaarMeasure] [μ.IsInvInvariant]
  (hsq : IsSquareIntegrableModCentralSubgroup C hC π.obj.representation μ)
  {I : Type uI} (ν : I → (M →* ℝ≥0ˣ))

/-- The actual canonical source form at every inducing representative,
using the same central quotient and Haar measure throughout the orbit. -/
def unitaryOrbitRepresentativeProductForm (A : UnitaryOrbitRepresentative ν π) :
    InvariantPositiveForm (productInducedCoefficientObject h hU A.val.obj).representation :=
  formalDegreeProductForm h hU hP K hK (compactFactorization K hPK) hG hδ
    A.val.obj hcof C hC μ
    (unitaryOrbitRepresentative_isDiscreteSeries ν π C hC μ hsq A) A.val.property.1

/-- Every actual inducing equivalence preserves the full canonical
inverse-degree product form at the representatives. -/
theorem unitaryOrbitRepresentativeProductForm_transport
    (A B : UnitaryOrbitRepresentative ν π)
    (a : A.val.obj.representation.Equiv B.val.obj.representation)
    (F H : productInducedCoefficientObject h hU A.val.obj) :
    (unitaryOrbitRepresentativeProductForm
      h hU hP K hK hPK hG hδ π hcof C hC μ hsq ν B).inner
        (productInducedCoefficientTransport h hU a F)
        (productInducedCoefficientTransport h hU a H) =
      (unitaryOrbitRepresentativeProductForm
        h hU hP K hK hPK hG hδ π hcof C hC μ hsq ν A).inner F H :=
  congrArg (fun b => b.inner F H)
    (formalDegreeProductForm_ofEquiv h hU hP K hK (compactFactorization K hPK)
      hG hδ hcof C hC μ
      (unitaryOrbitRepresentative_isDiscreteSeries ν π C hC μ hsq A) A.val.property.1
      (unitaryOrbitRepresentative_isDiscreteSeries ν π C hC μ hsq B) B.val.property.1 a)

private def orbitRepresentativeAt
    (ω : discreteSeriesOrbit C hC μ ν (discreteSeriesClass C hC μ π hsq)) :
    UnitaryOrbitRepresentative ν π :=
  Classical.choose
    (unitaryOrbitRepresentativeDiscreteSeriesOrbit_surjective ν π C hC μ hsq ω)

omit [LocallyCompactSpace G] [SecondCountableTopology G]
  [MeasurableSpace G] [BorelSpace G] [BorelSpace (M ⧸ C)] [μ.IsInvInvariant] in
private theorem orbitRepresentativeAt_spec
    (ω : discreteSeriesOrbit C hC μ ν (discreteSeriesClass C hC μ π hsq)) :
    unitaryOrbitRepresentativeDiscreteSeriesOrbit ν π C hC μ hsq
      (orbitRepresentativeAt π C hC μ hsq ν ω) = ω :=
  Classical.choose_spec
    (unitaryOrbitRepresentativeDiscreteSeriesOrbit_surjective ν π C hC μ hsq ω)

private def equivalenceOfOrbitEquality (A B : UnitaryOrbitRepresentative ν π)
    (hab : unitaryOrbitRepresentativeDiscreteSeriesOrbit ν π C hC μ hsq A =
      unitaryOrbitRepresentativeDiscreteSeriesOrbit ν π C hC μ hsq B) :
    A.val.obj.representation.Equiv B.val.obj.representation := by
  have hclass : (Quotient.mk _ A.val :
      SmoothDualClass.{0, uG, uV} (k := ℂ) (G := M)) = Quotient.mk _ B.val :=
    congrArg (fun ω => ω.val.val) hab
  exact SmoothRep.equivOfIso
    ((irreducibleAdmissibleProperty (k := ℂ) (G := M)).ι.mapIso
      (Classical.choice (Quotient.exact hclass)))

variable (hν : ∀ i, Continuous (ν i)) (hr : Continuous h.projection)
  {J : Type uJ} [Fintype J]
  (e : unitaryUnramifiedCharacters ν ≃* (J → Circle))

/-- The scalar pairing on the actual discrete-series class orbit.
Its independence of the auxiliary representative is proved below. -/
def unitaryOrbitProductPairing
    (q r : productInducedSmoothOrbitSections ν π e h hU K hP hK hν hr hPK)
    (ω : discreteSeriesOrbit C hC μ ν (discreteSeriesClass C hC μ π hsq)) : ℂ :=
  let A := orbitRepresentativeAt π C hC μ hsq ν ω
  (unitaryOrbitRepresentativeProductForm
    h hU hP K hK hPK hG hδ π hcof C hC μ hsq ν A).inner (q.val A) (r.val A)

/-- The descended pairing can be evaluated at any actual representative.
Coherence and canonical form transport remove the auxiliary choice. -/
theorem unitaryOrbitProductPairing_representative
    (q r : productInducedSmoothOrbitSections ν π e h hU K hP hK hν hr hPK)
    (A : UnitaryOrbitRepresentative ν π) :
    unitaryOrbitProductPairing
        h hU hP K hK hPK hG hδ π hcof C hC μ hsq ν hν hr e q r
        (unitaryOrbitRepresentativeDiscreteSeriesOrbit ν π C hC μ hsq A) =
      (unitaryOrbitRepresentativeProductForm
        h hU hP K hK hPK hG hδ π hcof C hC μ hsq ν A).inner (q.val A) (r.val A) := by
  let B := orbitRepresentativeAt π C hC μ hsq ν
    (unitaryOrbitRepresentativeDiscreteSeriesOrbit ν π C hC μ hsq A)
  let a := equivalenceOfOrbitEquality π C hC μ hsq ν B A
    (orbitRepresentativeAt_spec π C hC μ hsq ν _)
  have hp := unitaryOrbitRepresentativeProductForm_transport
    h hU hP K hK hPK hG hδ π hcof C hC μ hsq ν B A a (q.val B) (r.val B)
  rw [← q.property.1 B A a, ← r.property.1 B A a] at hp
  exact hp.symm

/-- The actual character parameterization recovers the previously
constructed inverse-degree fiber pairing, with no change of normalization. -/
theorem unitaryOrbitProductPairing_parameter
    (q r : productInducedSmoothOrbitSections ν π e h hU K hP hK hν hr hPK)
    (z : J → Circle) :
    unitaryOrbitProductPairing
        h hU hP K hK hPK hG hδ π hcof C hC μ hsq ν hν hr e q r
        (discreteSeriesOrbitMap C hC μ ν (discreteSeriesClass C hC μ π hsq) (e.symm z)) =
      (unitaryTorusProductForm
        h hU hP K hK hPK hG hδ π hcof C hC μ hsq ν e z).inner
        (q.val (unitaryOrbitParameterRepresentative ν π e z))
        (r.val (unitaryOrbitParameterRepresentative ν π e z)) :=
  unitaryOrbitProductPairing_representative
    h hU hP K hK hPK hG hδ π hcof C hC μ hsq ν hν hr e q r
    (unitaryOrbitParameterRepresentative ν π e z)

/-- Finite scalar smoothness in continuous torus coordinates gives
continuity on the actual orbit's stabilizer-quotient topology. -/
theorem continuous_unitaryOrbitProductPairing (he : Continuous e)
    (q r : productInducedSmoothOrbitSections ν π e h hU K hP hK hν hr hPK) :
    Continuous (unitaryOrbitProductPairing
      h hU hP K hK hPK hG hδ π hcof C hC μ hsq ν hν hr e q r) := by
  apply (isOpenQuotientMap_discreteSeriesOrbitMap
    C hC μ ν (discreteSeriesClass C hC μ π hsq)).isQuotientMap.continuous_iff.mpr
  have hp := (isSmooth_unitaryTorusProductForm_pairing
    h hU hP K hK hPK hG hδ π hcof C hC μ hsq ν hν hr e
    (productInducedSmoothOrbitFamilyEquiv ν π e h hU K hP hK hν hr hPK q)
    (productInducedSmoothOrbitFamilyEquiv ν π e h hU K hP hK hν hr hPK r)).continuous.comp he
  convert hp using 1
  funext χ
  change unitaryOrbitProductPairing
      h hU hP K hK hPK hG hδ π hcof C hC μ hsq ν hν hr e q r
      (discreteSeriesOrbitMap C hC μ ν (discreteSeriesClass C hC μ π hsq) χ) =
    (unitaryTorusProductForm
      h hU hP K hK hPK hG hδ π hcof C hC μ hsq ν e (e χ)).inner
      (q.val (unitaryOrbitParameterRepresentative ν π e (e χ)))
      (r.val (unitaryOrbitParameterRepresentative ν π e (e χ)))
  simpa only [e.symm_apply_apply] using
    unitaryOrbitProductPairing_parameter
      h hU hP K hK hPK hG hδ π hcof C hC μ hsq ν hν hr e q r (e χ)

/-- The scalar pairing on the torus is continuous by its actual finite
scalar-smooth family model. -/
theorem continuous_unitaryOrbitProductPairing_torus
    (q r : productInducedSmoothOrbitSections ν π e h hU K hP hK hν hr hPK) :
    Continuous (fun z =>
      (unitaryTorusProductForm
        h hU hP K hK hPK hG hδ π hcof C hC μ hsq ν e z).inner
        (q.val (unitaryOrbitParameterRepresentative ν π e z))
        (r.val (unitaryOrbitParameterRepresentative ν π e z))) := by
  change Continuous (fun z =>
    (unitaryTorusProductForm
      h hU hP K hK hPK hG hδ π hcof C hC μ hsq ν e z).inner
      ((productInducedSmoothOrbitFamilyEquiv ν π e h hU K hP hK hν hr hPK q).val z)
      ((productInducedSmoothOrbitFamilyEquiv ν π e h hU K hP hK hν hr hPK r).val z))
  exact (isSmooth_unitaryTorusProductForm_pairing
    h hU hP K hK hPK hG hδ π hcof C hC μ hsq ν hν hr e
    (productInducedSmoothOrbitFamilyEquiv ν π e h hU K hP hK hν hr hPK q)
    (productInducedSmoothOrbitFamilyEquiv ν π e h hU K hP hK hν hr hPK r)).continuous

variable [Finite (M ⧸ (commonNormKernel ν ⊔ C))]

local instance orbitStabilizerFinite :
    Finite (discreteSeriesStabilizer C hC μ ν (discreteSeriesClass C hC μ π hsq)) :=
  finite_discreteSeriesStabilizer ν C hC μ (discreteSeriesClass C hC μ π hsq)

/-- The torus cover carries the source character measure divided by the
cardinality of the actual class stabilizer. -/
def unitaryOrbitParameterMeasure
    (η : Measure (unitaryUnramifiedCharacters ν)) : Measure (J → Circle) :=
  (Nat.card (discreteSeriesStabilizer C hC μ ν
    (discreteSeriesClass C hC μ π hsq)) : ℝ≥0∞)⁻¹ • Measure.map e η

omit [LocallyCompactSpace G] [SecondCountableTopology G] [MeasurableSpace G]
  [BorelSpace G] [BorelSpace (M ⧸ C)] [μ.IsInvInvariant] [Fintype J] in
private theorem orbitStabilizerCard_ne_zero :
    (Nat.card (discreteSeriesStabilizer C hC μ ν
      (discreteSeriesClass C hC μ π hsq)) : ℝ≥0∞) ≠ 0 := by
  exact_mod_cast (Nat.card_pos (α := discreteSeriesStabilizer C hC μ ν
    (discreteSeriesClass C hC μ π hsq))).ne'

instance isFiniteMeasure_unitaryOrbitParameterMeasure
    (η : Measure (unitaryUnramifiedCharacters ν)) [IsFiniteMeasure η] :
    IsFiniteMeasure (unitaryOrbitParameterMeasure π C hC μ hsq ν e η) :=
  (Measure.map e η).smul_finite
    (ENNReal.inv_ne_top.mpr (orbitStabilizerCard_ne_zero π C hC μ hsq ν))

omit [LocallyCompactSpace G] [SecondCountableTopology G] [MeasurableSpace G]
  [BorelSpace G] [BorelSpace (M ⧸ C)] [μ.IsInvInvariant]
  [Finite (M ⧸ (commonNormKernel ν ⊔ C))] in
/-- Continuity and surjectivity of the coordinates preserve positivity on
nonempty open sets; the finite-fiber factor is strictly positive. -/
theorem isOpenPosMeasure_unitaryOrbitParameterMeasure (he : Continuous e)
    (η : Measure (unitaryUnramifiedCharacters ν)) [η.IsOpenPosMeasure] :
    (unitaryOrbitParameterMeasure π C hC μ hsq ν e η).IsOpenPosMeasure := by
  let := he.isOpenPosMeasure_map (μ := η) e.surjective
  exact Measure.isOpenPosMeasure_smul (μ := Measure.map e η) (by simp)

omit [LocallyCompactSpace G] [SecondCountableTopology G] [MeasurableSpace G]
  [BorelSpace G] [BorelSpace (M ⧸ C)] [μ.IsInvInvariant]
  [Finite (M ⧸ (commonNormKernel ν ⊔ C))] in
/-- This is the actual cover mass, with no probability normalization. -/
theorem unitaryOrbitParameterMeasure_univ (he : Continuous e)
    (η : Measure (unitaryUnramifiedCharacters ν)) :
    unitaryOrbitParameterMeasure π C hC μ hsq ν e η Set.univ =
      (Nat.card (discreteSeriesStabilizer C hC μ ν
        (discreteSeriesClass C hC μ π hsq)) : ℝ≥0∞)⁻¹ * η Set.univ := by
  simp [unitaryOrbitParameterMeasure, Measure.map_apply he.measurable]

/-- The normalized actual-orbit integral and its torus-cover expression
agree, retaining the original character measure and finite-fiber scale. -/
theorem integral_unitaryOrbitProductPairing_eq_parameterIntegral (he : Continuous e)
    (η : Measure (unitaryUnramifiedCharacters ν))
    (q r : productInducedSmoothOrbitSections ν π e h hU K hP hK hν hr hPK) :
    (∫ ω, unitaryOrbitProductPairing
      h hU hP K hK hPK hG hδ π hcof C hC μ hsq ν hν hr e q r ω
      ∂discreteSeriesOrbitMeasure ν C hC μ (discreteSeriesClass C hC μ π hsq) η) =
    ∫ z, (unitaryTorusProductForm
      h hU hP K hK hPK hG hδ π hcof C hC μ hsq ν e z).inner
      (q.val (unitaryOrbitParameterRepresentative ν π e z))
      (r.val (unitaryOrbitParameterRepresentative ν π e z))
      ∂unitaryOrbitParameterMeasure π C hC μ hsq ν e η := by
  rw [discreteSeriesOrbitMeasure, unitaryOrbitParameterMeasure]
  simp only [integral_smul_measure]
  rw [integral_map_of_stronglyMeasurable
    (continuous_discreteSeriesOrbitMap C hC μ ν
      (discreteSeriesClass C hC μ π hsq)).measurable
    (continuous_unitaryOrbitProductPairing
      h hU hP K hK hPK hG hδ π hcof C hC μ hsq ν hν hr e he q r
      ).measurable.stronglyMeasurable,
    integral_map_of_stronglyMeasurable he.measurable
      (continuous_unitaryOrbitProductPairing_torus
        h hU hP K hK hPK hG hδ π hcof C hC μ hsq ν hν hr e q r
        ).measurable.stronglyMeasurable]
  congr 1
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun χ => by
    simpa only [e.symm_apply_apply] using
      unitaryOrbitProductPairing_parameter
        h hU hP K hK hPK hG hδ π hcof C hC μ hsq ν hν hr e q r (e χ)

/-- The normalized orbit pairing is genuinely Bochner integrable.
Bounded scalar smoothness on the finite torus proves convergence. -/
theorem integrable_unitaryOrbitProductPairing (he : Continuous e)
    (η : Measure (unitaryUnramifiedCharacters ν)) [IsFiniteMeasure η]
    (q r : productInducedSmoothOrbitSections ν π e h hU K hP hK hν hr hPK) :
    Integrable (unitaryOrbitProductPairing
      h hU hP K hK hPK hG hδ π hcof C hC μ hsq ν hν hr e q r)
      (discreteSeriesOrbitMeasure ν C hC μ
        (discreteSeriesClass C hC μ π hsq) η) := by
  rw [discreteSeriesOrbitMeasure]
  apply Integrable.smul_measure _
    (ENNReal.inv_ne_top.mpr (orbitStabilizerCard_ne_zero π C hC μ hsq ν))
  apply (integrable_map_measure
    (continuous_unitaryOrbitProductPairing
      h hU hP K hK hPK hG hδ π hcof C hC μ hsq ν hν hr e he q r
      ).measurable.stronglyMeasurable.aestronglyMeasurable
    (continuous_discreteSeriesOrbitMap C hC μ ν
      (discreteSeriesClass C hC μ π hsq)).measurable.aemeasurable).mpr
  have hp := ((BoundedContinuousFunction.mkOfCompact
    ⟨_, continuous_unitaryOrbitProductPairing_torus
      h hU hP K hK hPK hG hδ π hcof C hC μ hsq ν hν hr e q r⟩
    ).compContinuous ⟨e, he⟩).integrable η
  convert hp using 1
  funext χ
  change unitaryOrbitProductPairing
      h hU hP K hK hPK hG hδ π hcof C hC μ hsq ν hν hr e q r
      (discreteSeriesOrbitMap C hC μ ν (discreteSeriesClass C hC μ π hsq) χ) =
    (unitaryTorusProductForm
      h hU hP K hK hPK hG hδ π hcof C hC μ hsq ν e (e χ)).inner
      (q.val (unitaryOrbitParameterRepresentative ν π e (e χ)))
      (r.val (unitaryOrbitParameterRepresentative ν π e (e χ)))
  simpa only [e.symm_apply_apply] using
    unitaryOrbitProductPairing_parameter
      h hU hP K hK hPK hG hδ π hcof C hC μ hsq ν hν hr e q r (e χ)

/-- The positive orbit-integral core on actual coherent smooth sections.
Its measure is the source's locally preserved measure when the supplied
character measure is invariant. -/
@[instance_reducible]
def productInducedSmoothOrbitCore (he : Continuous e)
    (η : Measure (unitaryUnramifiedCharacters ν))
    [IsFiniteMeasure η] [η.IsOpenPosMeasure] :
    InnerProductSpace.Core ℂ
      (productInducedSmoothOrbitSections ν π e h hU K hP hK hν hr hPK) := by
  letI := isOpenPosMeasure_unitaryOrbitParameterMeasure π C hC μ hsq ν e he η
  exact productInducedSmoothOrbitCoverCore
    h hU hP K hK hPK hG hδ π hcof C hC μ hsq ν hν hr e
    (unitaryOrbitParameterMeasure π C hC μ hsq ν e η)

/-- The entire positive core is the convergent integral of the descended
canonical inverse-degree fiber pairing over the actual class orbit. -/
theorem productInducedSmoothOrbitCore_inner_integral (he : Continuous e)
    (η : Measure (unitaryUnramifiedCharacters ν))
    [IsFiniteMeasure η] [η.IsOpenPosMeasure]
    (q r : productInducedSmoothOrbitSections ν π e h hU K hP hK hν hr hPK) :
    (productInducedSmoothOrbitCore
      h hU hP K hK hPK hG hδ π hcof C hC μ hsq ν hν hr e he η).inner q r =
      ∫ ω, unitaryOrbitProductPairing
        h hU hP K hK hPK hG hδ π hcof C hC μ hsq ν hν hr e q r ω
        ∂discreteSeriesOrbitMeasure ν C hC μ
          (discreteSeriesClass C hC μ π hsq) η := by
  let := isOpenPosMeasure_unitaryOrbitParameterMeasure π C hC μ hsq ν e he η
  exact (productInducedSmoothOrbitCoverCore_inner_integral
    h hU hP K hK hPK hG hδ π hcof C hC μ hsq ν hν hr e
    (unitaryOrbitParameterMeasure π C hC μ hsq ν e η) q r).trans
      (integral_unitaryOrbitProductPairing_eq_parameterIntegral
        h hU hP K hK hPK hG hδ π hcof C hC μ hsq ν hν hr e he η q r).symm

local instance productInducedOrbitFormTensorAddCommGroup :
    AddCommGroup
      (smoothFiniteTorusFunctions J ⊗[ℂ] ProductInducedCompactPicture h K π.obj) :=
  TensorProduct.addCommGroup

/-- The concrete diagonal invariant tensor model preserves the entire
actual-orbit integral, with the same finite-fiber factor on its cover. -/
theorem productInducedSmoothTensorOrbitEquiv_orbit_inner (he : Continuous e)
    (η : Measure (unitaryUnramifiedCharacters ν))
    [IsFiniteMeasure η] [η.IsOpenPosMeasure]
    (t u : (productInducedSmoothTensorRepresentation ν e h K hP hK hν hr π).invariants) :
    let := isOpenPosMeasure_unitaryOrbitParameterMeasure π C hC μ hsq ν e he η
    (productInducedSmoothOrbitCore
      h hU hP K hK hPK hG hδ π hcof C hC μ hsq ν hν hr e he η).inner
        (productInducedSmoothTensorOrbitEquiv ν π e h hU K hP hK hν hr hPK t)
        (productInducedSmoothTensorOrbitEquiv ν π e h hU K hP hK hν hr hPK u) =
      (productInducedSmoothInvariantTensorCore
        h hU hP K hK hPK hG hδ π hcof C hC μ hsq ν hν hr e
        (unitaryOrbitParameterMeasure π C hC μ hsq ν e η)).inner t u := by
  let := isOpenPosMeasure_unitaryOrbitParameterMeasure π C hC μ hsq ν e he η
  exact productInducedSmoothTensorOrbitEquiv_inner
    h hU hP K hK hPK hG hδ π hcof C hC μ hsq ν hν hr e
    (unitaryOrbitParameterMeasure π C hC μ hsq ν e η) t u

end Langlands.Plancherel
