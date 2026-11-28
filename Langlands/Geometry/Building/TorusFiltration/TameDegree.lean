import Langlands.BruhatTits.IntegralModels.InducedTorusShallowIntegers
import Langlands.Geometry.Building.KPWeaklyInducedTorus
import Langlands.Galois.Local.SeparableUnramifiedCompletion
import Mathlib.RingTheory.RamificationInertia.Basic

/-! # Degrees of tame extensions of the maximal unramified field -/

noncomputable section

universe u

open IsLocalRing CategoryTheory
open Langlands.BruhatTits.IntegralModels Langlands.LocalField Langlands.LocalGalois.Separable
open scoped BigOperators NNReal ValuativeRel

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1500000
set_option synthInstance.maxHeartbeats 150000

namespace Langlands.Geometry.Building

private theorem ramificationIdx_eq_finrank_local {R S : Type u}
    [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    [CommRing S] [IsDomain S] [IsDiscreteValuationRing S]
    [Algebra R S] [IsLocalHom (algebraMap R S)] [Module.Finite R S] [Module.Flat R S]
    [IsAlgClosed (ResidueField R)] :
    (maximalIdeal S).ramificationIdx R = Module.finrank R S := by
  classical
  let p := maximalIdeal R
  let q := maximalIdeal S
  let : q.LiesOver p := ⟨(maximalIdeal_comap (algebraMap R S)).symm⟩
  have hset : p.primesOver S = {q} := IsLocalRing.primesOver_eq S (IsDiscreteValuationRing.not_a_field R)
  let q₀ : p.primesOver S := ⟨q, by rw [hset]; exact Set.mem_singleton q⟩
  let : Unique (p.primesOver S) := ⟨⟨q₀⟩, fun a => Subtype.ext (by
    exact Set.mem_singleton_iff.mp (hset ▸ a.property))⟩
  let : Fintype (p.primesOver S) := Fintype.ofSubsingleton q₀
  have hdeg : q.inertiaDeg R = 1 := by
    rw [Ideal.inertiaDeg_eq_of_isMaximal p q]
    change Module.finrank (ResidueField R) (ResidueField S) = 1
    let : Algebra.IsIntegral R (ResidueField S) := Algebra.IsIntegral.trans S
    let : Algebra.IsIntegral (ResidueField R) (ResidueField S) := Algebra.IsIntegral.tower_top R
    let e := AlgEquiv.ofBijective (Algebra.ofId (ResidueField R) (ResidueField S))
      IsAlgClosed.algebraMap_bijective_of_isIntegral
    rw [← e.toLinearEquiv.finrank_eq, Module.finrank_self]
  have h := Ideal.sum_ramification_inertia_eq_finrank p S
  rw [Fintype.sum_unique] at h
  change q.ramificationIdx R * q.inertiaDeg R = _ at h
  simpa only [hdeg, mul_one] using h

section Fields

variable (F : Type u) [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]

local notation "O" => fixedFieldIntegers F
local notation "K" => inertiaFixedField F
local notation "Ω" => SeparableClosure F
local notation "ν" => algebraicExtensionAddValuation F Ω

private local instance fixedDVR : IsDiscreteValuationRing O :=
  fixedFieldIntegersIsDVR_of_valuesFromBase F (fixedFieldValuesFromBase F)

private def uniformizerInteger : 𝒪[F] :=
  ⟨LocalField.uniformizer F, (FML.ord_nonneg_iff_mem_integer F _).mp (by
    rw [LocalField.ord_uniformizer]
    exact zero_le_one)⟩

private theorem uniformizerInteger_irreducible : Irreducible (uniformizerInteger F) := by
  apply (IsDiscreteValuationRing.irreducible_iff_uniformizer _).mpr
  let a := uniformizerInteger F
  let v := ValuativeRel.valuation F
  have ha : (a : F) = LocalField.uniformizer F := rfl
  have hPos (z : 𝒪[F]) : z ∈ maximalIdeal (𝒪[F]) ↔ 0 < FML.ord F (z : F) := by
    change z ∈ maximalIdeal v.valuationSubring ↔ _
    rw [Valuation.mem_maximalIdeal_iff _ v, ← v.vlt_one_iff, ← FML.ord_lt_ord_iff, FML.ord_one]
  apply le_antisymm
  · intro z hz
    have hOrd := (hPos z).mp hz
    have hOrd' : 1 ≤ FML.ord F (z : F) := by
      rcases eq_or_ne (FML.ord F (z : F)) ⊤ with h | h
      · rw [h]
        exact le_top
      · obtain ⟨n, hn⟩ := WithTop.ne_top_iff_exists.mp h
        rw [← hn] at hOrd ⊢
        exact_mod_cast (show 1 ≤ n by exact Int.add_one_le_iff.mpr (by exact_mod_cast hOrd))
    change z ∈ (Ideal.span {a} : Set 𝒪[F])
    rw [Valuation.integer.coe_span_singleton_eq_setOfPred_le_v_coe]
    apply (v.vle_iff_le).mp
    apply (FML.ord_le_ord_iff F (a : F) (z : F)).mp
    rwa [ha, LocalField.ord_uniformizer]
  · apply (Ideal.span_singleton_le_iff_mem _).mpr
    rw [hPos, ha, LocalField.ord_uniformizer]
    exact zero_lt_one

/-- The order-one uniformizer used for coefficient depths generates the
maximal ideal of the unramified integer ring. -/
theorem maximalIdeal_eq_span_depthUniformizer :
    maximalIdeal O = Ideal.span {InducedTorusShallow.baseUniformizer F} := by
  have h : integerToFixedField F (uniformizerInteger F) = InducedTorusShallow.baseUniformizer F :=
    Subtype.ext rfl
  rw [← h]
  exact UnramifiedCompletion.maximalIdeal_before_eq_span_uniformizer F (uniformizerInteger_irreducible F)

variable (E : IntermediateField (inertiaFixedField F) (SeparableClosure F))
  [FiniteDimensional (inertiaFixedField F) E]

local notation "B" => ConnectedImage.integers F E

private local instance extensionAlgebra : Algebra O E :=
  ((algebraMap K E).comp (algebraMap O K)).toAlgebra

private local instance extensionTower : IsScalarTower O K E :=
  IsScalarTower.of_algebraMap_eq' rfl

private local instance extensionIntegersTower : IsScalarTower O B E :=
  IsScalarTower.of_algebraMap_eq' rfl

omit [FiniteDimensional K E] in
private theorem intermediateIntegers_map_injective : Function.Injective (algebraMap O B) :=
  fun _ _ h => Subtype.ext ((algebraMap K E).injective
    (congrArg (fun z : B => (z : E)) h))

private theorem intermediateIntegers_localHom : IsLocalHom (algebraMap O B) := by
  let : Module.Finite O B := IsIntegralClosure.finite O K E B
  exact (algebraMap_isIntegral_iff.mpr (inferInstance : Algebra.IsIntegral O B)).isLocalHom
    (intermediateIntegers_map_injective F E)

private theorem intermediateIntegers_dvr : IsDiscreteValuationRing B := by
  let : IsDedekindDomain B := IsIntegralClosure.isDedekindDomain O K E B
  let : IsLocalHom (algebraMap O B) := intermediateIntegers_localHom F E
  refine { not_a_field' := ?_ }
  intro h
  have hm := maximalIdeal_comap (algebraMap O B)
  rw [h, ← RingHom.ker_eq_comap_bot, (RingHom.injective_iff_ker_eq_bot _).mp
    (intermediateIntegers_map_injective F E)] at hm
  exact (IsDiscreteValuationRing.not_a_field O) hm.symm

set_option maxHeartbeats 1900000 in
private theorem integralUniformizer_power_value :
    ∃ ϖ : B, Irreducible ϖ ∧ (Module.finrank K E) • ν ((ϖ : E) : Ω) = 1 := by
  let π := InducedTorusShallow.baseUniformizer F
  let : IsDiscreteValuationRing B := intermediateIntegers_dvr F E
  let : IsLocalHom (algebraMap O B) := intermediateIntegers_localHom F E
  let : IsAlgClosed (ResidueField O) := (fixedFieldResidueIsAlgClosure F).isAlgClosed
  let : Module.Finite O B := IsIntegralClosure.finite O K E B
  let : Module.IsTorsionFree O E :=
    Module.isTorsionFree_iff_algebraMap_injective.mpr
      ((algebraMap K E).injective.comp (IsFractionRing.injective O K))
  let : Module.Free O B := IsIntegralClosure.module_free O K E _
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible B
  have hπ : algebraMap O B π ≠ 0 := (map_ne_zero_iff _ (intermediateIntegers_map_injective F E)).mpr
    (InducedTorusShallow.baseUniformizer_ne_zero F)
  obtain ⟨n, u, hu⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hπ hϖ
  have hmap : (maximalIdeal O).map (algebraMap O B) = (maximalIdeal B) ^ n := by
    rw [maximalIdeal_eq_span_depthUniformizer F, Ideal.map_span, Set.image_singleton,
      hϖ.maximalIdeal_eq, Ideal.span_singleton_pow]
    exact Ideal.span_singleton_eq_span_singleton.mpr
      (Associated.symm ⟨u, by simpa only [mul_comm] using hu.symm⟩)
  have hn : (maximalIdeal B).ramificationIdx O = n := by
    let : (maximalIdeal B).LiesOver (maximalIdeal O) := ⟨(maximalIdeal_comap (algebraMap O B)).symm⟩
    have hne : (maximalIdeal O).map (algebraMap O B) ≠ ⊥ := by
      rw [maximalIdeal_eq_span_depthUniformizer F, Ideal.map_span, Set.image_singleton]
      intro h
      exact hπ (Ideal.span_singleton_eq_bot.mp h)
    rw [Ideal.IsDedekindDomain.ramificationIdx_eq_multiplicity (maximalIdeal O) (maximalIdeal B) hne,
      hmap]
    exact multiplicity_pow_self_of_prime
      (Ideal.prime_of_isPrime (IsDiscreteValuationRing.not_a_field B) inferInstance) n
  have hDim : n = Module.finrank K E :=
    hn.symm.trans ((ramificationIdx_eq_finrank_local (R := O) (S := B)).trans
      (IsIntegralClosure.rank O K E B))
  have hu₀ : ν (((u : B) : E) : Ω) = 0 := by
    change negativeLogValue (localLogScale F) (intermediateValuation F E ((u : B) : E)) = 0
    rw [(ConnectedImage.isUnit_integers_iff F E _).mp u.isUnit, negativeLogValue_one]
  refine ⟨ϖ, hϖ, ?_⟩
  have h := congrArg (fun a : B => ν ((a : E) : Ω)) hu
  change ν ((π : K) : Ω) = ν ((((u : B) : E) : Ω) * (((ϖ : E) : Ω) ^ n)) at h
  rw [InducedTorusShallow.baseUniformizer_value, AddValuation.map_mul, AddValuation.map_pow,
    hu₀, zero_add, hDim] at h
  exact h.symm

set_option maxHeartbeats 1900000 in
theorem not_dvd_finrank_of_tame (hE : IsTamelyRamifiedOverUnramifiedClosure F E) :
    ¬ ringChar 𝓀[F] ∣ Module.finrank K E := by
  obtain ⟨ϖ, hϖ, hn⟩ := integralUniformizer_power_value F E
  have hϖ₀ : ((ϖ : E) : Ω) ≠ 0 := fun h => hϖ.ne_zero (Subtype.ext (Subtype.ext h))
  obtain ⟨m, _, hprime, hvalue⟩ := hE
  obtain ⟨a, ha⟩ := hvalue (ϖ : E) (fun h => hϖ₀ (congrArg Subtype.val h))
  have hv : sepClosureValuation F (((ϖ : E) : Ω) ^ m) =
      sepClosureValuation F (algebraMap F Ω a) := by rw [map_pow]; exact ha
  have ha₀ : a ≠ 0 := by
    intro h
    have he : (((ϖ : E) : Ω) ^ m) = 0 := (Valuation.zero_iff _).mp
      (by rw [hv, h, map_zero, map_zero])
    exact pow_ne_zero _ hϖ₀ he
  obtain ⟨l, hl⟩ := WithTop.ne_top_iff_exists.mp ((FML.ord_ne_top_iff F).mpr ha₀)
  have hν := congrArg (negativeLogValue (localLogScale F)) hv
  change ν ((((ϖ : E) : Ω)) ^ m) = ν (algebraMap F Ω a) at hν
  rw [AddValuation.map_pow, algebraicExtensionAddValuation_base_of_ord_eq F Ω hl.symm] at hν
  obtain ⟨t, ht⟩ := WithTop.ne_top_iff_exists.mp ((ν).ne_top_iff.mpr hϖ₀)
  rw [← ht, ← WithTop.coe_nsmul] at hn hν
  have hn' : (Module.finrank K E : ℝ) * t = 1 := by
    rw [← nsmul_eq_mul]
    exact WithTop.coe_injective (hn.trans (WithTop.coe_one).symm)
  have hm'Value : (m : ℝ) * t = l := by
    rw [← nsmul_eq_mul]
    exact WithTop.coe_injective hν
  have hreal : (m : ℝ) = (Module.finrank K E : ℝ) * (l : ℝ) := by
    calc
      (m : ℝ) = (m : ℝ) * ((Module.finrank K E : ℝ) * t) := by rw [hn', mul_one]
      _ = (Module.finrank K E : ℝ) * (l : ℝ) := by rw [mul_left_comm, hm'Value]
  have hm' : (m : ℤ) = (Module.finrank K E : ℤ) * l := by exact_mod_cast hreal
  intro h
  have hh : (ringChar 𝓀[F] : ℤ) ∣ (m : ℤ) := by
    rw [hm']
    exact dvd_mul_of_dvd_left (Int.natCast_dvd_natCast.mpr h) l
  exact hprime (Int.natCast_dvd_natCast.mp hh)

end Fields
end Langlands.Geometry.Building
