import Langlands.Representation.Plancherel.ProductInducedOrbitForm
import Langlands.Representation.Plancherel.ProductInducedOrbitBaseChange

/-! # Base-object independence of actual orbit pairings and integral cores -/

noncomputable section

set_option maxHeartbeats 800000
set_option maxRecDepth 4096

open CategoryTheory MeasureTheory
open scoped NNReal ENNReal

namespace Langlands.Plancherel

open Aubert.General HarishChandraSchwartz Induction CompactInduction

universe uG uI uV uJ

variable {G : Type uG} [Group G] [TopologicalSpace G] [NonarchimedeanGroup G]
  {M : Subgroup G} {I : Type uI} (ν : I → (M →* ℝ≥0ˣ))
  (π : IrreducibleAdmissibleRep.{0, uG, uV} (k := ℂ) (G := M))
  (C : Subgroup M) [C.Normal] (hC : C ≤ Subgroup.center M)
  [MeasurableSpace (M ⧸ C)]
  (μ : Measure (M ⧸ C)) [μ.IsHaarMeasure]
  (hsq : IsSquareIntegrableModCentralSubgroup C hC π.obj.representation μ)
  (A : UnitaryOrbitRepresentative ν π)

private theorem representative_discreteSeriesOrbit_eq :
    MulAction.orbit (unitaryUnramifiedCharacters ν)
        (discreteSeriesClass C hC μ A.val
          (unitaryOrbitRepresentative_isDiscreteSeries ν π C hC μ hsq A)) =
      MulAction.orbit (unitaryUnramifiedCharacters ν)
        (discreteSeriesClass C hC μ π hsq) := by
  obtain ⟨χ, hχ⟩ := A.property
  have hbase : χ • discreteSeriesClass C hC μ π hsq =
      discreteSeriesClass C hC μ A.val
        (unitaryOrbitRepresentative_isDiscreteSeries ν π C hC μ hsq A) :=
    Subtype.ext hχ
  rw [← hbase]
  exact MulAction.orbit_smul χ _

/-- Recenter the actual discrete-series orbit without changing its classes.
The topology is the original stabilizer-quotient topology at each base. -/
def unitaryOrbitDiscreteSeriesBaseHomeomorph :
    discreteSeriesOrbit C hC μ ν (discreteSeriesClass C hC μ A.val
      (unitaryOrbitRepresentative_isDiscreteSeries ν π C hC μ hsq A)) ≃ₜ
        discreteSeriesOrbit C hC μ ν (discreteSeriesClass C hC μ π hsq) where
  toEquiv := Set.equivOfEq (representative_discreteSeriesOrbit_eq ν π C hC μ hsq A)
  continuous_toFun := by
    obtain ⟨χ, hχ⟩ := A.property
    have hbase : χ • discreteSeriesClass C hC μ π hsq =
        discreteSeriesClass C hC μ A.val
          (unitaryOrbitRepresentative_isDiscreteSeries ν π C hC μ hsq A) :=
      Subtype.ext hχ
    apply (isOpenQuotientMap_discreteSeriesOrbitMap C hC μ ν
      (discreteSeriesClass C hC μ A.val
        (unitaryOrbitRepresentative_isDiscreteSeries ν π C hC μ hsq A))
      ).isQuotientMap.continuous_iff.mpr
    convert (continuous_discreteSeriesOrbitMap C hC μ ν
      (discreteSeriesClass C hC μ π hsq)).comp (continuous_id.mul_const χ) using 1
    funext η
    apply Subtype.ext
    change η • discreteSeriesClass C hC μ A.val _ =
      (η * χ) • discreteSeriesClass C hC μ π hsq
    rw [mul_smul, hbase]
  continuous_invFun := by
    obtain ⟨χ, hχ⟩ := A.property
    have hbase : χ • discreteSeriesClass C hC μ π hsq =
        discreteSeriesClass C hC μ A.val
          (unitaryOrbitRepresentative_isDiscreteSeries ν π C hC μ hsq A) :=
      Subtype.ext hχ
    apply (isOpenQuotientMap_discreteSeriesOrbitMap C hC μ ν
      (discreteSeriesClass C hC μ π hsq)).isQuotientMap.continuous_iff.mpr
    convert (continuous_discreteSeriesOrbitMap C hC μ ν
      (discreteSeriesClass C hC μ A.val
        (unitaryOrbitRepresentative_isDiscreteSeries ν π C hC μ hsq A))
      ).comp (continuous_id.mul_const χ⁻¹) using 1
    funext η
    apply Subtype.ext
    change η • discreteSeriesClass C hC μ π hsq =
      (η * χ⁻¹) • discreteSeriesClass C hC μ A.val _
    rw [← hbase, mul_smul, inv_smul_smul]

@[simp]
theorem unitaryOrbitDiscreteSeriesBaseHomeomorph_val
    (ω : discreteSeriesOrbit C hC μ ν (discreteSeriesClass C hC μ A.val
      (unitaryOrbitRepresentative_isDiscreteSeries ν π C hC μ hsq A))) :
    (unitaryOrbitDiscreteSeriesBaseHomeomorph ν π C hC μ hsq A ω).val = ω.val := rfl

@[simp]
theorem unitaryOrbitDiscreteSeriesBaseHomeomorph_symm_val
    (ω : discreteSeriesOrbit C hC μ ν (discreteSeriesClass C hC μ π hsq)) :
    ((unitaryOrbitDiscreteSeriesBaseHomeomorph ν π C hC μ hsq A).symm ω).val =
      ω.val := rfl

/-- The same actual classes have the same actual character stabilizer,
so no new finite-fiber normalization is introduced on recentering. -/
theorem unitaryOrbitDiscreteSeriesStabilizer_eq :
    discreteSeriesStabilizer C hC μ ν (discreteSeriesClass C hC μ A.val
        (unitaryOrbitRepresentative_isDiscreteSeries ν π C hC μ hsq A)) =
      discreteSeriesStabilizer C hC μ ν (discreteSeriesClass C hC μ π hsq) := by
  obtain ⟨χ, hχ⟩ := A.property
  have hbase : χ • discreteSeriesClass C hC μ π hsq =
      discreteSeriesClass C hC μ A.val
        (unitaryOrbitRepresentative_isDiscreteSeries ν π C hC μ hsq A) :=
    Subtype.ext hχ
  rw [← hbase, discreteSeriesStabilizer_unitaryTwist]

/-- Reindexing all actual representatives commutes with the identity on
actual discrete-series classes. -/
theorem unitaryOrbitRepresentativeDiscreteSeriesOrbit_baseChange
    (B : UnitaryOrbitRepresentative ν A.val) :
    unitaryOrbitDiscreteSeriesBaseHomeomorph ν π C hC μ hsq A
        (unitaryOrbitRepresentativeDiscreteSeriesOrbit ν A.val C hC μ
          (unitaryOrbitRepresentative_isDiscreteSeries ν π C hC μ hsq A) B) =
      unitaryOrbitRepresentativeDiscreteSeriesOrbit ν π C hC μ hsq
        ((unitaryOrbitRepresentativeBaseEquiv ν π A).symm B) := by
  apply Subtype.ext
  rfl

/-- The identity on actual orbit classes pushes forward the measure at
the new actual representative to the old one, with its original scale. -/
theorem map_unitaryOrbitDiscreteSeriesBaseHomeomorph_measure
    [Finite (discreteSeriesStabilizer C hC μ ν (discreteSeriesClass C hC μ π hsq))]
    [Finite (discreteSeriesStabilizer C hC μ ν (discreteSeriesClass C hC μ A.val
      (unitaryOrbitRepresentative_isDiscreteSeries ν π C hC μ hsq A)))]
    (η : Measure (unitaryUnramifiedCharacters ν)) [η.IsMulLeftInvariant] :
    Measure.map (unitaryOrbitDiscreteSeriesBaseHomeomorph ν π C hC μ hsq A)
        (discreteSeriesOrbitMeasure ν C hC μ
          (discreteSeriesClass C hC μ A.val
            (unitaryOrbitRepresentative_isDiscreteSeries ν π C hC μ hsq A)) η) =
      discreteSeriesOrbitMeasure ν C hC μ (discreteSeriesClass C hC μ π hsq) η := by
  obtain ⟨χ, hχ⟩ := A.property
  have hbase : χ • discreteSeriesClass C hC μ π hsq =
      discreteSeriesClass C hC μ A.val
        (unitaryOrbitRepresentative_isDiscreteSeries ν π C hC μ hsq A) :=
    Subtype.ext hχ
  have hcomp :
      (unitaryOrbitDiscreteSeriesBaseHomeomorph ν π C hC μ hsq A) ∘
        discreteSeriesOrbitMap C hC μ ν (discreteSeriesClass C hC μ A.val
          (unitaryOrbitRepresentative_isDiscreteSeries ν π C hC μ hsq A)) =
      (discreteSeriesOrbitMap C hC μ ν (discreteSeriesClass C hC μ π hsq)) ∘
        (χ * ·) := by
    funext ξ
    apply Subtype.ext
    change ξ • discreteSeriesClass C hC μ A.val _ =
      (χ * ξ) • discreteSeriesClass C hC μ π hsq
    rw [mul_comm χ ξ, mul_smul, hbase]
  rw [discreteSeriesOrbitMeasure,
    Measure.map_smul _ (unitaryOrbitDiscreteSeriesBaseHomeomorph
      ν π C hC μ hsq A).continuous.measurable.aemeasurable,
    Measure.map_map (unitaryOrbitDiscreteSeriesBaseHomeomorph
      ν π C hC μ hsq A).continuous.measurable
      (continuous_discreteSeriesOrbitMap C hC μ ν
        (discreteSeriesClass C hC μ A.val
          (unitaryOrbitRepresentative_isDiscreteSeries ν π C hC μ hsq A))).measurable,
    hcomp, ← Measure.map_map (f := fun ξ => χ * ξ)
      (continuous_discreteSeriesOrbitMap C hC μ ν
        (discreteSeriesClass C hC μ π hsq)).measurable (measurable_const_mul χ),
    map_mul_left_eq_self, unitaryOrbitDiscreteSeriesStabilizer_eq]
  rfl

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
  (hcof : CompactOpenCofinal M)
  [BorelSpace (M ⧸ C)] [μ.IsInvInvariant]
  (hν : ∀ i, Continuous (ν i)) (hr : Continuous h.projection)
  {J : Type uJ} [Fintype J]
  (e : unitaryUnramifiedCharacters ν ≃* (J → Circle))

/-- Actual section base change preserves the descended scalar pairing at
every actual class, using the same central quotient and canonical degree. -/
theorem unitaryOrbitProductPairing_baseChange
    (q r : productInducedSmoothOrbitSections ν π e h hU K hP hK hν hr hPK)
    (ω : discreteSeriesOrbit C hC μ ν (discreteSeriesClass C hC μ A.val
      (unitaryOrbitRepresentative_isDiscreteSeries ν π C hC μ hsq A))) :
    unitaryOrbitProductPairing h hU hP K hK hPK hG hδ A.val hcof C hC μ
        (unitaryOrbitRepresentative_isDiscreteSeries ν π C hC μ hsq A) ν hν hr e
        (productInducedSmoothOrbitBaseEquiv ν π A h hU e K hP hK hν hr hPK q)
        (productInducedSmoothOrbitBaseEquiv ν π A h hU e K hP hK hν hr hPK r) ω =
      unitaryOrbitProductPairing h hU hP K hK hPK hG hδ π hcof C hC μ hsq ν hν hr e
        q r (unitaryOrbitDiscreteSeriesBaseHomeomorph ν π C hC μ hsq A ω) := by
  obtain ⟨B, rfl⟩ := unitaryOrbitRepresentativeDiscreteSeriesOrbit_surjective ν A.val
    C hC μ (unitaryOrbitRepresentative_isDiscreteSeries ν π C hC μ hsq A) ω
  rw [unitaryOrbitProductPairing_representative,
    unitaryOrbitRepresentativeDiscreteSeriesOrbit_baseChange,
    unitaryOrbitProductPairing_representative]
  rfl

variable [Finite (M ⧸ (commonNormKernel ν ⊔ C))]

local instance originalBaseStabilizerFinite :
    Finite (discreteSeriesStabilizer C hC μ ν (discreteSeriesClass C hC μ π hsq)) :=
  finite_discreteSeriesStabilizer ν C hC μ (discreteSeriesClass C hC μ π hsq)

local instance newBaseStabilizerFinite :
    Finite (discreteSeriesStabilizer C hC μ ν (discreteSeriesClass C hC μ A.val
      (unitaryOrbitRepresentative_isDiscreteSeries ν π C hC μ hsq A))) :=
  finite_discreteSeriesStabilizer ν C hC μ (discreteSeriesClass C hC μ A.val
    (unitaryOrbitRepresentative_isDiscreteSeries ν π C hC μ hsq A))

omit [LocallyCompactSpace G] [SecondCountableTopology G] [MeasurableSpace G]
  [BorelSpace G] [BorelSpace (M ⧸ C)] [μ.IsInvInvariant] [Fintype J]
  [Finite (M ⧸ (commonNormKernel ν ⊔ C))] in
/-- The source-scaled torus measure has exactly the same finite-fiber
factor at any actual base representative; invariance is not needed here. -/
theorem unitaryOrbitParameterMeasure_baseChange
    (η : Measure (unitaryUnramifiedCharacters ν)) :
    unitaryOrbitParameterMeasure A.val C hC μ
        (unitaryOrbitRepresentative_isDiscreteSeries ν π C hC μ hsq A) ν e η =
      unitaryOrbitParameterMeasure π C hC μ hsq ν e η := by
  rw [unitaryOrbitParameterMeasure, unitaryOrbitParameterMeasure,
    unitaryOrbitDiscreteSeriesStabilizer_eq]

/-- The actual scalar integral is unchanged by any actual unitary-orbit
base representative. Character invariance cancels the parameter translation. -/
theorem integral_unitaryOrbitProductPairing_baseChange (he : Continuous e)
    (η : Measure (unitaryUnramifiedCharacters ν)) [η.IsMulLeftInvariant]
    (q r : productInducedSmoothOrbitSections ν π e h hU K hP hK hν hr hPK) :
    (∫ ω, unitaryOrbitProductPairing h hU hP K hK hPK hG hδ A.val hcof C hC μ
        (unitaryOrbitRepresentative_isDiscreteSeries ν π C hC μ hsq A) ν hν hr e
        (productInducedSmoothOrbitBaseEquiv ν π A h hU e K hP hK hν hr hPK q)
        (productInducedSmoothOrbitBaseEquiv ν π A h hU e K hP hK hν hr hPK r) ω
      ∂discreteSeriesOrbitMeasure ν C hC μ (discreteSeriesClass C hC μ A.val
        (unitaryOrbitRepresentative_isDiscreteSeries ν π C hC μ hsq A)) η) =
      ∫ ω, unitaryOrbitProductPairing h hU hP K hK hPK hG hδ π hcof C hC μ hsq
        ν hν hr e q r ω
        ∂discreteSeriesOrbitMeasure ν C hC μ (discreteSeriesClass C hC μ π hsq) η := by
  rw [← map_unitaryOrbitDiscreteSeriesBaseHomeomorph_measure ν π C hC μ hsq A η,
    integral_map_of_stronglyMeasurable
      (unitaryOrbitDiscreteSeriesBaseHomeomorph ν π C hC μ hsq A).continuous.measurable
      (continuous_unitaryOrbitProductPairing
        h hU hP K hK hPK hG hδ π hcof C hC μ hsq ν hν hr e he q r
        ).measurable.stronglyMeasurable]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun ω =>
    unitaryOrbitProductPairing_baseChange
      ν π C hC μ hsq A h hU hP K hK hPK hG hδ hcof hν hr e q r ω

/-- The existing actual-object section equivalence preserves the whole
positive integral core, with the same invariant source character measure. -/
theorem productInducedSmoothOrbitBaseEquiv_inner (he : Continuous e)
    (η : Measure (unitaryUnramifiedCharacters ν))
    [η.IsMulLeftInvariant] [IsFiniteMeasure η] [η.IsOpenPosMeasure]
    (q r : productInducedSmoothOrbitSections ν π e h hU K hP hK hν hr hPK) :
    (productInducedSmoothOrbitCore h hU hP K hK hPK hG hδ A.val hcof C hC μ
        (unitaryOrbitRepresentative_isDiscreteSeries ν π C hC μ hsq A)
        ν hν hr e he η).inner
        (productInducedSmoothOrbitBaseEquiv ν π A h hU e K hP hK hν hr hPK q)
        (productInducedSmoothOrbitBaseEquiv ν π A h hU e K hP hK hν hr hPK r) =
      (productInducedSmoothOrbitCore h hU hP K hK hPK hG hδ π hcof C hC μ hsq
        ν hν hr e he η).inner q r := by
  rw [productInducedSmoothOrbitCore_inner_integral,
    productInducedSmoothOrbitCore_inner_integral]
  exact integral_unitaryOrbitProductPairing_baseChange
    ν π C hC μ hsq A h hU hP K hK hPK hG hδ hcof hν hr e he η q r

end Langlands.Plancherel
