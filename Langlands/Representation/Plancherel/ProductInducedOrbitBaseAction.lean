import Langlands.Representation.Plancherel.ProductInducedOrbitCoefficients
import Langlands.Representation.Plancherel.ProductInducedOrbitFormBaseChange

/-! # Actual base-object comparisons of the full smooth orbit representation -/

noncomputable section

set_option maxHeartbeats 800000
set_option maxRecDepth 4096

open CategoryTheory MeasureTheory
open scoped NNReal

namespace Langlands.Plancherel

open Aubert.General HarishChandraSchwartz

universe uG uI uV uJ

variable {G : Type uG} [Group G] [TopologicalSpace G] [LocallyCompactSpace G]
  [NonarchimedeanGroup G] {P M U : Subgroup G}
  (h : IsSemidirectDecomposition P M U) (hU : IsClosed (U : Set G))
  {I : Type uI} (ν : I → (M →* ℝ≥0ˣ))
  (π : IrreducibleAdmissibleRep.{0, uG, uV} (k := ℂ) (G := M))
  (A : UnitaryOrbitRepresentative ν π)
  {J : Type uJ} [Fintype J]
  (e : unitaryUnramifiedCharacters ν ≃* (J → Circle))
  (K : OpenSubgroup G) (hP : IsClosed (P : Set G)) (hK : IsCompact (K : Set G))
  (hν : ∀ i, Continuous (ν i)) (hr : Continuous h.projection)
  (hPK : ∀ g : G, ∃ p : P, ∃ k : K, g = (p : G) * (k : G))

/-- Actual base-object reindexing intertwines the full product actions:
each actual inducing object and its section value are retained. -/
theorem productInducedSmoothOrbitBaseEquiv_action
    (he : HasLaurentUnitaryCoordinates ν e) (x : G × G)
    (q : productInducedSmoothOrbitSections ν π e h hU K hP hK hν hr hPK) :
    productInducedSmoothOrbitBaseEquiv ν π A h hU e K hP hK hν hr hPK
        (productInducedSmoothOrbitRepresentation h hU ν π K hP hK hν hr hPK e he x q) =
      productInducedSmoothOrbitRepresentation h hU ν A.val K hP hK hν hr hPK e he x
        (productInducedSmoothOrbitBaseEquiv ν π A h hU e K hP hK hν hr hPK q) :=
  Subtype.ext rfl

/-- The existing actual section reindexing as an equivalence of full actions. -/
def productInducedSmoothOrbitBaseRepresentationEquiv
    (he : HasLaurentUnitaryCoordinates ν e) :
    Representation.Equiv
      (productInducedSmoothOrbitRepresentation h hU ν π K hP hK hν hr hPK e he)
      (productInducedSmoothOrbitRepresentation h hU ν A.val K hP hK hν hr hPK e he) :=
  Representation.Equiv.mk
    (productInducedSmoothOrbitBaseEquiv ν π A h hU e K hP hK hν hr hPK)
    (fun x => LinearMap.ext
      (productInducedSmoothOrbitBaseEquiv_action h hU ν π A e K hP hK hν hr hPK he x))

/-- Changing the actual base object within its orbit gives an isomorphism
in the canonical smooth representation category, with the original reindexing. -/
def productInducedSmoothOrbitBaseIso
    (he : HasLaurentUnitaryCoordinates ν e) :
    productInducedSmoothOrbitObject h hU ν π K hP hK hν hr hPK e he ≅
      productInducedSmoothOrbitObject h hU ν A.val K hP hK hν hr hPK e he :=
  SmoothRep.mkIso
    (productInducedSmoothOrbitBaseRepresentationEquiv h hU ν π A e K hP hK hν hr hPK he)

@[simp]
theorem productInducedSmoothOrbitBaseIso_hom_apply
    (he : HasLaurentUnitaryCoordinates ν e)
    (q : productInducedSmoothOrbitSections ν π e h hU K hP hK hν hr hPK) :
    SmoothRep.hom
        (productInducedSmoothOrbitBaseIso h hU ν π A e K hP hK hν hr hPK he).hom q =
      productInducedSmoothOrbitBaseEquiv ν π A h hU e K hP hK hν hr hPK q := rfl

section Coefficients

variable [SecondCountableTopology G] [T2Space G] [MeasurableSpace G] [BorelSpace G]
  [LocallyCompactSpace P]
  (hG : ∀ g : G, Measure.modularCharacter g = 1)
  (hδ : ∀ p : P, Measure.modularCharacter p =
    (HaarModulus.closedRestrictCharacter U hU P h.le_normalizer p : ℝ≥0))
  (C : Subgroup M) [C.Normal] (hC : C ≤ Subgroup.center M)
  [MeasurableSpace (M ⧸ C)]
  (μ : Measure (M ⧸ C)) [μ.IsHaarMeasure]
  (hsq : IsSquareIntegrableModCentralSubgroup C hC π.obj.representation μ)

/-- The actual coefficient is independent of the actual base inducing object,
after the published identity homeomorphism of the two actual orbit spaces. -/
theorem unitaryOrbitCoefficientMap_baseChange
    (q : productInducedSmoothOrbitSections ν π e h hU K hP hK hν hr hPK)
    (w : discreteSeriesOrbit C hC μ ν (discreteSeriesClass C hC μ A.val
      (unitaryOrbitRepresentative_isDiscreteSeries ν π C hC μ hsq A))) :
    unitaryOrbitCoefficientMap h hU hP K hK hPK hG hδ ν A.val hν hr C hC μ
        (unitaryOrbitRepresentative_isDiscreteSeries ν π C hC μ hsq A) e
        (productInducedSmoothOrbitBaseEquiv ν π A h hU e K hP hK hν hr hPK q) w =
      unitaryOrbitCoefficientMap h hU hP K hK hPK hG hδ ν π hν hr C hC μ hsq e q
        (unitaryOrbitDiscreteSeriesBaseHomeomorph ν π C hC μ hsq A w) := by
  obtain ⟨B, rfl⟩ := unitaryOrbitRepresentativeDiscreteSeriesOrbit_surjective ν A.val
    C hC μ (unitaryOrbitRepresentative_isDiscreteSeries ν π C hC μ hsq A) w
  rw [unitaryOrbitCoefficientMap_representative,
    unitaryOrbitRepresentativeDiscreteSeriesOrbit_baseChange,
    unitaryOrbitCoefficientMap_representative]
  rfl

end Coefficients

section OrbitForm

variable [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G]
  [LocallyCompactSpace P]
  (hG : ∀ g : G, Measure.modularCharacter g = 1)
  (hδ : ∀ p : P, Measure.modularCharacter p =
    (HaarModulus.closedRestrictCharacter U hU P h.le_normalizer p : ℝ≥0))
  (hcof : CompactOpenCofinal M)
  (C : Subgroup M) [C.Normal] (hC : C ≤ Subgroup.center M)
  [MeasurableSpace (M ⧸ C)] [BorelSpace (M ⧸ C)]
  (μ : Measure (M ⧸ C)) [μ.IsHaarMeasure] [μ.IsInvInvariant]
  (hsq : IsSquareIntegrableModCentralSubgroup C hC π.obj.representation μ)
  [Finite (M ⧸ (commonNormKernel ν ⊔ C))]

/-- Base-object comparison preserves the entire full invariant form by the
existing whole-core comparison with its original invariant character measure. -/
theorem productInducedSmoothOrbitBaseForm_inner
    (hLaurent : HasLaurentUnitaryCoordinates ν e) (he : Continuous e)
    (η : Measure (unitaryUnramifiedCharacters ν))
    [η.IsMulLeftInvariant] [IsFiniteMeasure η] [η.IsOpenPosMeasure]
    (q r : productInducedSmoothOrbitSections ν π e h hU K hP hK hν hr hPK) :
    (productInducedSmoothOrbitForm h hU ν A.val K hP hK hν hr hPK e hG hδ hcof C hC μ
      (unitaryOrbitRepresentative_isDiscreteSeries ν π C hC μ hsq A) hLaurent he η).inner
        (productInducedSmoothOrbitBaseEquiv ν π A h hU e K hP hK hν hr hPK q)
        (productInducedSmoothOrbitBaseEquiv ν π A h hU e K hP hK hν hr hPK r) =
      (productInducedSmoothOrbitForm h hU ν π K hP hK hν hr hPK e hG hδ hcof C hC μ
        hsq hLaurent he η).inner q r :=
  productInducedSmoothOrbitBaseEquiv_inner
    ν π C hC μ hsq A h hU hP K hK hPK hG hδ hcof hν hr e he η q r

/-- The actual-base comparison for the norms constructed from the original
orbit-integral cores. No norm on an inducing carrier is imposed. -/
def productInducedSmoothOrbitBaseIsometry (he : Continuous e)
    (η : Measure (unitaryUnramifiedCharacters ν))
    [η.IsMulLeftInvariant] [IsFiniteMeasure η] [η.IsOpenPosMeasure] :
    letI := (productInducedSmoothOrbitCore h hU hP K hK hPK hG hδ π hcof C hC μ hsq
      ν hν hr e he η).toNormedAddCommGroup
    letI := (productInducedSmoothOrbitCore h hU hP K hK hPK hG hδ A.val hcof C hC μ
      (unitaryOrbitRepresentative_isDiscreteSeries ν π C hC μ hsq A)
      ν hν hr e he η).toNormedAddCommGroup
    productInducedSmoothOrbitSections ν π e h hU K hP hK hν hr hPK ≃ₗᵢ[ℂ]
      productInducedSmoothOrbitSections ν A.val e h hU K hP hK hν hr hPK := by
  letI := (productInducedSmoothOrbitCore h hU hP K hK hPK hG hδ π hcof C hC μ hsq
    ν hν hr e he η).toNormedAddCommGroup
  letI := (productInducedSmoothOrbitCore h hU hP K hK hPK hG hδ A.val hcof C hC μ
    (unitaryOrbitRepresentative_isDiscreteSeries ν π C hC μ hsq A)
    ν hν hr e he η).toNormedAddCommGroup
  refine { productInducedSmoothOrbitBaseEquiv ν π A h hU e K hP hK hν hr hPK with
    norm_map' := ?_ }
  intro q
  change Real.sqrt (Complex.re
      ((productInducedSmoothOrbitCore h hU hP K hK hPK hG hδ A.val hcof C hC μ
        (unitaryOrbitRepresentative_isDiscreteSeries ν π C hC μ hsq A)
        ν hν hr e he η).inner
        (productInducedSmoothOrbitBaseEquiv ν π A h hU e K hP hK hν hr hPK q)
        (productInducedSmoothOrbitBaseEquiv ν π A h hU e K hP hK hν hr hPK q))) =
    Real.sqrt (Complex.re
      ((productInducedSmoothOrbitCore h hU hP K hK hPK hG hδ π hcof C hC μ hsq
        ν hν hr e he η).inner q q))
  rw [productInducedSmoothOrbitBaseEquiv_inner]

@[simp]
theorem productInducedSmoothOrbitBaseIsometry_apply
    (he : Continuous e) (η : Measure (unitaryUnramifiedCharacters ν))
    [η.IsMulLeftInvariant] [IsFiniteMeasure η] [η.IsOpenPosMeasure]
    (q : productInducedSmoothOrbitSections ν π e h hU K hP hK hν hr hPK)
    (B : UnitaryOrbitRepresentative ν A.val) :
    (productInducedSmoothOrbitBaseIsometry
      h hU ν π A e K hP hK hν hr hPK hG hδ hcof C hC μ hsq he η q).val B =
      q.val ((unitaryOrbitRepresentativeBaseEquiv ν π A).symm B) := rfl

/-- The actual-base isometry intertwines the full actual product actions. -/
theorem productInducedSmoothOrbitBaseIsometry_action
    (hLaurent : HasLaurentUnitaryCoordinates ν e) (he : Continuous e)
    (η : Measure (unitaryUnramifiedCharacters ν))
    [η.IsMulLeftInvariant] [IsFiniteMeasure η] [η.IsOpenPosMeasure]
    (x : G × G)
    (q : productInducedSmoothOrbitSections ν π e h hU K hP hK hν hr hPK) :
    productInducedSmoothOrbitBaseIsometry
        h hU ν π A e K hP hK hν hr hPK hG hδ hcof C hC μ hsq he η
        (productInducedSmoothOrbitRepresentation h hU ν π K hP hK hν hr hPK e hLaurent x q) =
      productInducedSmoothOrbitRepresentation h hU ν A.val K hP hK hν hr hPK e hLaurent x
        (productInducedSmoothOrbitBaseIsometry
          h hU ν π A e K hP hK hν hr hPK hG hδ hcof C hC μ hsq he η q) :=
  productInducedSmoothOrbitBaseEquiv_action h hU ν π A e K hP hK hν hr hPK hLaurent x q

end OrbitForm

end Langlands.Plancherel
