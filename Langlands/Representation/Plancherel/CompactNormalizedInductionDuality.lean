import Langlands.Representation.Plancherel.NormalizedInductionDualTensor
import Langlands.Analysis.Local.ModularCompactAverage
import Langlands.Representation.RankinSelberg.Measures
import Langlands.Group.LeftQuotientInversion

/-! # Probability compact-picture normalization for induction duality -/

noncomputable section

open MeasureTheory MeasureTheory.Measure Langlands.Aubert.General
open scoped NNReal

namespace Langlands.Plancherel.CompactInduction

universe uG uV

section Measure

variable {G : Type uG} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [LocallyCompactSpace G] [SecondCountableTopology G]
  [MeasurableSpace G] [BorelSpace G]
  (K : OpenSubgroup G) (hK : IsCompact (K : Set G))

/-- The intrinsic Haar probability on the supplied compact open subgroup,
constructed before choosing any inducing representation. -/
def measure : Measure K :=
  (RankinSelberg.normalizedCompactOpenHaar K hK).comap Subtype.val

instance measure_isHaar : IsHaarMeasure (measure K hK) :=
  IsHaarMeasure.comap (mH := inferInstance)
    (RankinSelberg.normalizedCompactOpenHaar K hK)
    (f := (K : Subgroup G).subtype) K.isOpen.isOpenEmbedding_subtypeVal

instance measure_isProbability : IsProbabilityMeasure (measure K hK) := by
  constructor
  have he := comap_subtype_coe_apply K.isOpen.measurableSet
    (RankinSelberg.normalizedCompactOpenHaar K hK)
    (Set.univ : Set K)
  rw [Set.image_univ, Subtype.range_coe] at he
  exact he.trans (RankinSelberg.normalizedCompactOpenHaar_self K hK)

variable {P : Subgroup G} [LocallyCompactSpace P] (hP : IsClosed (P : Set G))

include hP in

/-- The constructed probability measure has the full scalar right-invariance
law for modular-covariant locally constant functions when `G = P K`. -/
theorem measure_scalar
    (hG : ∀ g : G, modularCharacter g = 1)
    (hPK : ∀ g : G, ∃ q ∈ P, ∃ k ∈ K, g = q * k)
    (φ : G → ℂ) (hφ : IsLocallyConstant φ)
    (hcov : ∀ (q : P) (x : G), φ ((q : G) * x) =
      ((modularCharacter q : ℝ) : ℂ) * φ x) (g : G) :
    Integrable (fun k : K => φ ((k : G) * g)) (measure K hK) ∧
      (∫ k : K, φ ((k : G) * g) ∂measure K hK) =
        ∫ k : K, φ (k : G) ∂measure K hK := by
  let μ := RankinSelberg.normalizedCompactOpenHaar K hK
  let : IsMulRightInvariant μ := ⟨fun g => by
    rw [ModularCompactAverage.map_mul_right_eq_modularCharacter_smul μ g,
      hG g, one_smul]⟩
  let : CompactSpace K := isCompact_iff_compactSpace.mp hK
  refine ⟨?_, ?_⟩
  · exact (hφ.continuous.comp (continuous_subtype_val.mul continuous_const))
      |>.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  · have he := ModularCompactAverage.setIntegral_mul_right_eq μ P hP
      (K : Subgroup G) K.isOpen hK hPK φ hφ.continuous hcov g
    exact (integral_subtype_comap (μ := μ) K.isOpen.measurableSet
      (fun x => φ (x * g))).trans
        (he.trans (integral_subtype_comap (μ := μ) K.isOpen.measurableSet φ).symm)

end Measure

section Duality

variable {G : Type uG} [Group G] [TopologicalSpace G]
  [LocallyCompactSpace G] [NonarchimedeanGroup G] [T2Space G]
  [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G]
  {P M U : Subgroup G} [LocallyCompactSpace P]
  (h : IsSemidirectDecomposition P M U) (hU : IsClosed (U : Set G))
  (hP : IsClosed (P : Set G)) (hm : Continuous h.projection)
  (K : OpenSubgroup G) (hK : IsCompact (K : Set G))
  (hPK : ∀ g : G, ∃ q ∈ P, ∃ k ∈ K, g = q * k)
  (hG : ∀ g : G, modularCharacter g = 1)

variable (hδ : ∀ q : P, modularCharacter q =
  (HaarModulus.closedRestrictCharacter U hU P h.le_normalizer q : ℝ≥0))

include hP hm hPK hG hδ in
/-- Actual normalized-induction duality with its probability compact integral.
The scalar integration law is proved for the constructed measure. -/
theorem exists_integralDualEquiv
    (A : SmoothRep.{0, uG, uV} ℂ M) (hA : A.IsAdmissible) :
    ∃ E : Representation.Equiv
        ((normalizedInductionFunctor h hU).obj A).contragredient.representation
        ((normalizedInductionFunctor h hU).obj A.contragredient).representation,
      ∀ (ℓ : ((normalizedInductionFunctor h hU).obj A).contragredient)
        (f : (normalizedInductionFunctor h hU).obj A),
        smoothDualPairing ((normalizedInductionFunctor h hU).obj A).representation ℓ f =
          ∫ k : K, smoothDualPairing A.representation
            (Induction.eval P (inducingRepresentation h hU A.contragredient) (E ℓ) k)
            (Induction.eval P (inducingRepresentation h hU A) f k)
            ∂measure K hK := by
  let : CompactSpace (Induction.LeftQuotient P) :=
    Induction.compactSpace_leftQuotient_of_compact_representatives P hK hPK
  have hsq : ∀ q : P,
      ((HaarModulus.closedHalfCharacter U hU P h.le_normalizer q : ℂˣ) : ℂ) *
        HaarModulus.closedHalfCharacter U hU P h.le_normalizer q =
      ((modularCharacter q : ℝ) : ℂ) := by
    intro q
    rw [closedHalfCharacter_mul_self h hU q, hδ q]
  have : IsHaarMeasure (measure K hK) := measure_isHaar K hK
  obtain ⟨E, hE⟩ := Induction.exists_integralDualEquiv P h.projection
    (HaarModulus.closedHalfCharacter U hU P h.le_normalizer)
    (fun q => modularCharacter q) (K : Subgroup G) (measure K hK)
    hm (HaarModulus.isOpen_ker_closedHalfCharacter U hU P h.le_normalizer)
    hsq (compactOpenCofinal_of_isClosed (h.isClosed_levi hP hm))
    (measure_scalar K hK hP hG hPK) A.representation A.isSmooth
    (smoothInduced_inducingRepresentation_isAdmissible h hU hm A hA)
  exact exists_functorEquiv_of_twistEquiv h hU (K : Subgroup G)
    (measure K hK) A E hE

/-- Choose the equivalence furnished by the proved probability integral duality. -/
def integralDualEquiv
    (A : SmoothRep.{0, uG, uV} ℂ M) (hA : A.IsAdmissible) :
    Representation.Equiv
      ((normalizedInductionFunctor h hU).obj A).contragredient.representation
      ((normalizedInductionFunctor h hU).obj A.contragredient).representation :=
  Classical.choose (exists_integralDualEquiv h hU hP hm K hK hPK hG hδ A hA)

/-- The chosen equivalence has exactly the compact probability normalization. -/
theorem integralDualEquiv_pairing
    (A : SmoothRep.{0, uG, uV} ℂ M) (hA : A.IsAdmissible)
    (ℓ : ((normalizedInductionFunctor h hU).obj A).contragredient)
    (f : (normalizedInductionFunctor h hU).obj A) :
    smoothDualPairing ((normalizedInductionFunctor h hU).obj A).representation ℓ f =
      ∫ k : K, smoothDualPairing A.representation
        (Induction.eval P (inducingRepresentation h hU A.contragredient)
          (integralDualEquiv h hU hP hm K hK hPK hG hδ A hA ℓ) k)
        (Induction.eval P (inducingRepresentation h hU A) f k)
        ∂measure K hK :=
  Classical.choose_spec (exists_integralDualEquiv h hU hP hm K hK hPK hG hδ A hA) ℓ f

end Duality

end Langlands.Plancherel.CompactInduction
