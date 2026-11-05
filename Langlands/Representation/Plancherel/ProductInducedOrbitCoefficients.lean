import Langlands.Representation.Plancherel.ProductInducedOrbitFullAction
import Langlands.Representation.Plancherel.CompactProductFormTransport

/-! # Actual coefficient maps on coherent smooth orbit sections -/

noncomputable section

set_option maxHeartbeats 800000
set_option maxRecDepth 4096

open CategoryTheory MeasureTheory
open scoped NNReal TensorProduct

namespace Langlands.Plancherel

open Aubert.General Induction CompactInduction

universe uG uI uV uJ

variable {G : Type uG} [Group G] [TopologicalSpace G] {P M U : Subgroup G}

private theorem compactCoefficientFactorization (K : OpenSubgroup G)
    (hPK : ∀ g : G, ∃ p : P, ∃ k : K, g = (p : G) * (k : G)) (g : G) :
    ∃ p ∈ P, ∃ k ∈ K, g = p * k := by
  obtain ⟨p, k, hg⟩ := hPK g
  exact ⟨p, p.property, k, k.property, hg⟩

variable [LocallyCompactSpace G] [NonarchimedeanGroup G]
  [SecondCountableTopology G] [T2Space G] [MeasurableSpace G] [BorelSpace G]
  [LocallyCompactSpace P]
  (h : IsSemidirectDecomposition P M U) (hU : IsClosed (U : Set G))
  (hP : IsClosed (P : Set G)) (K : OpenSubgroup G) (hK : IsCompact (K : Set G))
  (hPK : ∀ g : G, ∃ p : P, ∃ k : K, g = (p : G) * (k : G))
  (hG : ∀ g : G, Measure.modularCharacter g = 1)
  (hδ : ∀ p : P, Measure.modularCharacter p =
    (HaarModulus.closedRestrictCharacter U hU P h.le_normalizer p : ℝ≥0))
  {I : Type uI} (ν : I → (M →* ℝ≥0ˣ))
  (π : IrreducibleAdmissibleRep.{0, uG, uV} (k := ℂ) (G := M))
  (hν : ∀ i, Continuous (ν i)) (hr : Continuous h.projection)

/-- The actual compact-probability coefficient map at every inducing representative. -/
def unitaryOrbitRepresentativeCoefficientMap (A : UnitaryOrbitRepresentative ν π) :
    productInducedCoefficientObject h hU A.val.obj →ₗ[ℂ] LocallyConstant G ℂ :=
  CompactInduction.coefficientMap h hU A.val.obj K hK hP hr
    (compactCoefficientFactorization K hPK) hG hδ A.val.property.2

/-- Every actual inducing equivalence preserves the coefficient function. -/
theorem unitaryOrbitRepresentativeCoefficientMap_transport
    (A B : UnitaryOrbitRepresentative ν π)
    (a : A.val.obj.representation.Equiv B.val.obj.representation)
    (F : productInducedCoefficientObject h hU A.val.obj) :
    unitaryOrbitRepresentativeCoefficientMap h hU hP K hK hPK hG hδ ν π hr B
        (productInducedCoefficientTransport h hU a F) =
      unitaryOrbitRepresentativeCoefficientMap h hU hP K hK hPK hG hδ ν π hr A F :=
  CompactInduction.coefficientMap_transport h hU hP K hK
    (compactCoefficientFactorization K hPK) hG hδ hr A.val.property.2 B.val.property.2 a F

variable (C : Subgroup M) [C.Normal] (hC : C ≤ Subgroup.center M)
  [MeasurableSpace (M ⧸ C)]
  (μ : Measure (M ⧸ C)) [μ.IsHaarMeasure]
  (hsq : IsSquareIntegrableModCentralSubgroup C hC π.obj.representation μ)

private def coefficientRepresentativeAt
    (ω : discreteSeriesOrbit C hC μ ν (discreteSeriesClass C hC μ π hsq)) :
    UnitaryOrbitRepresentative ν π :=
  Classical.choose
    (unitaryOrbitRepresentativeDiscreteSeriesOrbit_surjective ν π C hC μ hsq ω)

omit [LocallyCompactSpace G] [SecondCountableTopology G] [T2Space G]
  [MeasurableSpace G] [BorelSpace G] [LocallyCompactSpace P] in
private theorem coefficientRepresentativeAt_spec
    (ω : discreteSeriesOrbit C hC μ ν (discreteSeriesClass C hC μ π hsq)) :
    unitaryOrbitRepresentativeDiscreteSeriesOrbit ν π C hC μ hsq
      (coefficientRepresentativeAt ν π C hC μ hsq ω) = ω :=
  Classical.choose_spec
    (unitaryOrbitRepresentativeDiscreteSeriesOrbit_surjective ν π C hC μ hsq ω)

private def coefficientEquivalenceOfOrbitEquality (A B : UnitaryOrbitRepresentative ν π)
    (hab : unitaryOrbitRepresentativeDiscreteSeriesOrbit ν π C hC μ hsq A =
      unitaryOrbitRepresentativeDiscreteSeriesOrbit ν π C hC μ hsq B) :
    A.val.obj.representation.Equiv B.val.obj.representation := by
  have hclass : (Quotient.mk _ A.val :
      SmoothDualClass.{0, uG, uV} (k := ℂ) (G := M)) = Quotient.mk _ B.val :=
    congrArg (fun ω => ω.val.val) hab
  exact SmoothRep.equivOfIso
    ((irreducibleAdmissibleProperty (k := ℂ) (G := M)).ι.mapIso
      (Classical.choice (Quotient.exact hclass)))

variable {J : Type uJ} [Fintype J]
  (e : unitaryUnramifiedCharacters ν ≃* (J → Circle))

/-- The actual coefficient function of a smooth section at each discrete-series
orbit class, with its original compact probability normalization. -/
def unitaryOrbitCoefficientMap :
    productInducedSmoothOrbitSections ν π e h hU K hP hK hν hr hPK →ₗ[ℂ]
      (discreteSeriesOrbit C hC μ ν (discreteSeriesClass C hC μ π hsq) → LocallyConstant G ℂ) where
  toFun q ω :=
    let A := coefficientRepresentativeAt ν π C hC μ hsq ω
    unitaryOrbitRepresentativeCoefficientMap h hU hP K hK hPK hG hδ ν π hr A (q.val A)
  map_add' q r := by
    funext ω
    exact map_add _ _ _
  map_smul' c q := by
    funext ω
    exact map_smul _ c _

/-- Coherence and coefficient transport remove the auxiliary representative choice. -/
theorem unitaryOrbitCoefficientMap_representative
    (q : productInducedSmoothOrbitSections ν π e h hU K hP hK hν hr hPK)
    (A : UnitaryOrbitRepresentative ν π) :
    unitaryOrbitCoefficientMap h hU hP K hK hPK hG hδ ν π hν hr C hC μ hsq e q
        (unitaryOrbitRepresentativeDiscreteSeriesOrbit ν π C hC μ hsq A) =
      unitaryOrbitRepresentativeCoefficientMap h hU hP K hK hPK hG hδ ν π hr A (q.val A) := by
  let B := coefficientRepresentativeAt ν π C hC μ hsq
    (unitaryOrbitRepresentativeDiscreteSeriesOrbit ν π C hC μ hsq A)
  let a := coefficientEquivalenceOfOrbitEquality ν π C hC μ hsq B A
    (coefficientRepresentativeAt_spec ν π C hC μ hsq _)
  have ht := unitaryOrbitRepresentativeCoefficientMap_transport
    h hU hP K hK hPK hG hδ ν π hr B A a (q.val B)
  rw [← q.property.1 B A a] at ht
  exact ht.symm

/-- At every actual representative this map is its literal diagonal compact integral. -/
theorem unitaryOrbitCoefficientMap_integral_representative
    (q : productInducedSmoothOrbitSections ν π e h hU K hP hK hν hr hPK)
    (A : UnitaryOrbitRepresentative ν π) (g : G) :
    unitaryOrbitCoefficientMap h hU hP K hK hPK hG hδ ν π hν hr C hC μ hsq e q
        (unitaryOrbitRepresentativeDiscreteSeriesOrbit ν π C hC μ hsq A) g =
      ∫ k : K, CompactInduction.integrand h hU A.val.obj K g (q.val A) k
        ∂CompactInduction.measure K hK := by
  rw [unitaryOrbitCoefficientMap_representative]
  exact CompactInduction.coefficientMap_integral h hU A.val.obj K hK hP hr
    (compactCoefficientFactorization K hPK) hG hδ A.val.property.2 (q.val A) g

/-- Pullback along actual character parameters recovers the actual fiber coefficient. -/
theorem unitaryOrbitCoefficientMap_parameter
    (q : productInducedSmoothOrbitSections ν π e h hU K hP hK hν hr hPK) (z : J → Circle) :
    unitaryOrbitCoefficientMap h hU hP K hK hPK hG hδ ν π hν hr C hC μ hsq e q
        (discreteSeriesOrbitMap C hC μ ν (discreteSeriesClass C hC μ π hsq) (e.symm z)) =
      unitaryOrbitRepresentativeCoefficientMap h hU hP K hK hPK hG hδ ν π hr
        (unitaryOrbitParameterRepresentative ν π e z)
        (q.val (unitaryOrbitParameterRepresentative ν π e z)) :=
  unitaryOrbitCoefficientMap_representative
    h hU hP K hK hPK hG hδ ν π hν hr C hC μ hsq e q
    (unitaryOrbitParameterRepresentative ν π e z)

/-- The full product action becomes the original right and inverse-left translations. -/
theorem unitaryOrbitCoefficientMap_action
    (hLaurent : HasLaurentUnitaryCoordinates ν e) (x : G × G)
    (q : productInducedSmoothOrbitSections ν π e h hU K hP hK hν hr hPK)
    (ω : discreteSeriesOrbit C hC μ ν (discreteSeriesClass C hC μ π hsq)) (g : G) :
    unitaryOrbitCoefficientMap h hU hP K hK hPK hG hδ ν π hν hr C hC μ hsq e
        (productInducedSmoothOrbitRepresentation h hU ν π K hP hK hν hr hPK e hLaurent x q) ω g =
      unitaryOrbitCoefficientMap h hU hP K hK hPK hG hδ ν π hν hr C hC μ hsq e q ω
        (x.2⁻¹ * g * x.1) := by
  obtain ⟨A, rfl⟩ :=
    unitaryOrbitRepresentativeDiscreteSeriesOrbit_surjective ν π C hC μ hsq ω
  rw [unitaryOrbitCoefficientMap_representative, unitaryOrbitCoefficientMap_representative]
  exact CompactInduction.coefficientMap_action h hU A.val.obj K hK hP hr
    (compactCoefficientFactorization K hPK) hG hδ A.val.property.2 x (q.val A) g

/-- One compact open subgroup fixes both translations of all coefficients of
the entire section, simultaneously at every actual orbit class. -/
theorem unitaryOrbitCoefficientMap_biInvariant
    (q : productInducedSmoothOrbitSections ν π e h hU K hP hK hν hr hPK) :
    ∃ H : OpenSubgroup G, H ≤ K ∧ IsCompact (H : Set G) ∧
      ∀ (ω : discreteSeriesOrbit C hC μ ν (discreteSeriesClass C hC μ π hsq))
        (k l : H) (g : G),
        unitaryOrbitCoefficientMap h hU hP K hK hPK hG hδ ν π hν hr C hC μ hsq e q ω
            ((k : G) * g * (l : G)) =
          unitaryOrbitCoefficientMap h hU hP K hK hPK hG hδ ν π hν hr C hC μ hsq e q ω g := by
  obtain ⟨H, hHK, hHc, hH⟩ := productInducedSmoothOrbitSections_exists_product_stabilizer
    h hU ν π K hP hK hν hr hPK e q
  refine ⟨H, hHK, hHc, ?_⟩
  intro ω k l g
  obtain ⟨A, rfl⟩ :=
    unitaryOrbitRepresentativeDiscreteSeriesOrbit_surjective ν π C hC μ hsq ω
  rw [unitaryOrbitCoefficientMap_representative]
  let x : H.prod H := ⟨((l : G), (k : G)⁻¹), l.property, H.inv_mem k.property⟩
  have hfix : (productInducedCoefficientObject h hU A.val.obj).representation x (q.val A) = q.val A :=
    congrFun (hH x) A
  have ht := CompactInduction.coefficientMap_action h hU A.val.obj K hK hP hr
    (compactCoefficientFactorization K hPK) hG hδ A.val.property.2 x (q.val A) g
  have hc := congrArg (fun F => unitaryOrbitRepresentativeCoefficientMap
    h hU hP K hK hPK hG hδ ν π hr A F g) hfix
  simpa only [x, inv_inv, unitaryOrbitRepresentativeCoefficientMap] using ht.symm.trans hc

end Langlands.Plancherel
