import Langlands.BushnellKutzko.MinimalElement
import Langlands.LocalField.FiniteExtension

/-! # Arithmetic of the integral closure for a finite local-field extension -/

noncomputable section

open ValuativeRel IsLocalRing IsDiscreteValuationRing

namespace Langlands.BushnellKutzko

universe uF uE

variable (F : Type uF) [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F] (E : Type uE) [Field E] [Algebra F E]

section Spectral

variable [FiniteDimensional F E]

local instance baseNorm : NontriviallyNormedField F := LocalGalois.localNormedField F
local instance baseUltrametric : IsUltrametricDist F := LocalGalois.localNormedField_ultrametric F
local instance baseComplete : CompleteSpace F := LocalGalois.localNormedField_complete F

private theorem integral_iff_mem_spectral (x : E) :
    IsIntegral 𝒪[F] x ↔ x ∈ LocalGalois.extensionIntegers F E := by
  let b : LocalGalois.baseIntegers F ≃+* 𝒪[F] :=
    RingEquiv.subringCongr (LocalGalois.localNormedField_integer F)
  rw [← LocalGalois.integral_iff_mem_spectralIntegers F E]
  constructor
  · intro h
    exact h.map_of_comp_eq b.symm.toRingHom (RingHom.id E) (by ext a; rfl)
  · intro h
    exact h.map_of_comp_eq b.toRingHom (RingHom.id E) (by ext a; rfl)

private theorem subfieldInteger_subring_eq :
    letI := LocalField.FiniteExtension.valuativeRel F E
    (subfieldIntegers F E).toSubring = (valuation E).integer := by
  let := LocalField.FiniteExtension.valuativeRel F E
  ext x
  change IsIntegral 𝒪[F] x ↔ valuation E x ≤ 1
  rw [integral_iff_mem_spectral F E]
  have : (LocalGalois.spectralValuation F E).Compatible :=
    Valuation.Compatible.ofValuation _
  change LocalGalois.spectralValuation F E x ≤ 1 ↔ valuation E x ≤ 1
  rw [← Valuation.vle_one_iff (LocalGalois.spectralValuation F E),
    Valuation.vle_one_iff (valuation E)]

/-- The integral closure is the integer ring of the actual spectral local field. -/
def subfieldIntegerEquiv :
    letI := LocalField.FiniteExtension.valuativeRel F E
    subfieldIntegers F E ≃+* 𝒪[E] :=
  RingEquiv.subringCongr (subfieldInteger_subring_eq F E)

/-- The integral closure of the base integer ring is a discrete valuation ring. -/
theorem subfieldIntegers_isDiscreteValuationRing : IsDiscreteValuationRing (subfieldIntegers F E) := by
  let := LocalField.FiniteExtension.normedField F E
  let := LocalField.FiniteExtension.valuativeRel F E
  let := LocalField.FiniteExtension.isLocalField F E
  exact IsDiscreteValuationRing.RingEquivClass.isDiscreteValuationRing
    (subfieldIntegerEquiv F E).symm

/-- The original extension field is the field of fractions of its integer ring. -/
theorem subfieldIntegers_isFractionRing : IsFractionRing (subfieldIntegers F E) E := by
  let := LocalField.FiniteExtension.valuativeRel F E
  exact IsFractionRing.of_ringEquiv_left (subfieldIntegerEquiv F E) (fun _ => rfl)

end Spectral

omit [TopologicalSpace F] [IsNonarchimedeanLocalField F] in
/-- In the discrete valuation ring, the published Jacobson radical is its maximal ideal. -/
theorem subfieldMaximalIdeal_eq [IsLocalRing (subfieldIntegers F E)] :
    subfieldMaximalIdeal F E = maximalIdeal (subfieldIntegers F E) :=
  ringJacobson_eq_maximalIdeal (subfieldIntegers F E)

section Ramification

variable [IsDiscreteValuationRing (subfieldIntegers F E)]

/-- Extension of the base maximal ideal is the corresponding power of the extension ideal. -/
theorem map_baseMaximalIdeal :
    (𝓂[F]).map (algebraMap 𝒪[F] (subfieldIntegers F E)) =
      subfieldMaximalIdeal F E ^ subfieldRamificationIndex F E := by
  classical
  let P := IsLocalRing.maximalIdeal (subfieldIntegers F E)
  have : Algebra.IsIntegral 𝒪[F] (subfieldIntegers F E) := inferInstanceAs
    (Algebra.IsIntegral 𝒪[F] (integralClosure 𝒪[F] E))
  have : FaithfulSMul 𝒪[F] (subfieldIntegers F E) := by
    apply (faithfulSMul_iff_algebraMap_injective _ _).mpr
    intro x y hxy
    exact Subtype.ext ((algebraMap F E).injective
      (congrArg (fun z : subfieldIntegers F E => (z : E)) hxy))
  have : Module.IsTorsionFree 𝒪[F] (subfieldIntegers F E) :=
    Module.IsTorsionFree.trans_faithfulSMul 𝒪[F] (subfieldIntegers F E) (subfieldIntegers F E)
  have : P.IsMaximal := inferInstanceAs
    ((IsLocalRing.maximalIdeal (subfieldIntegers F E)).IsMaximal)
  have : P.LiesOver (𝓂[F]) := ⟨(eq_maximalIdeal (inferInstance : (P.under 𝒪[F]).IsMaximal)).symm⟩
  have hprime : (𝓂[F]).primesOver (subfieldIntegers F E) = {P} := by
    ext Q
    constructor
    · intro hQ
      exact Set.mem_singleton_iff.mpr (eq_maximalIdeal (Ideal.isMaximal_of_mem_primesOver hQ))
    · intro hQ
      obtain rfl := Set.mem_singleton_iff.mp hQ
      exact ⟨inferInstance, inferInstance⟩
  have hbase : (𝓂[F] : Ideal 𝒪[F]) ≠ ⊥ := IsDiscreteValuationRing.not_a_field _
  rw [Ideal.map_algebraMap_eq_finsetProd_pow (R := subfieldIntegers F E) hbase,
    Finset.prod_eq_single P]
  · simp [subfieldRamificationIndex, subfieldMaximalIdeal_eq, P]
  · intro Q hQ hne
    exact (hne (by simpa [hprime] using hQ)).elim
  · simp [hprime]

/-- The image of a base uniformizer is an extension uniformizer to the ramification index,
up to a unit. -/
theorem baseUniformizer_factorization {π : 𝒪[F]} {ϖ : subfieldIntegers F E}
    (hπ : Irreducible π) (hϖ : Irreducible ϖ) :
    ∃ u : (subfieldIntegers F E)ˣ,
      algebraMap 𝒪[F] (subfieldIntegers F E) π =
        (u : subfieldIntegers F E) * ϖ ^ subfieldRamificationIndex F E := by
  have h := map_baseMaximalIdeal F E
  rw [hπ.maximalIdeal_eq, Ideal.map_span, Set.image_singleton,
    subfieldMaximalIdeal_eq, hϖ.maximalIdeal_eq, Ideal.span_singleton_pow] at h
  have ha := Ideal.span_singleton_eq_span_singleton.mp h
  obtain ⟨u, hu⟩ := ha.symm
  exact ⟨u, by simpa [mul_comm] using hu.symm⟩

end Ramification

end Langlands.BushnellKutzko
