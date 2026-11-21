import Langlands.Geometry.FormalGroup.DrinfeldSubfieldCharacters
import Mathlib.RingTheory.DiscreteValuationRing.TFAE

/-! # The cyclic expansion in the actual local division order -/

noncomputable section

open scoped BigOperators

namespace Langlands.FormalGroup.LocalDivision

open ValuativeRel CentralDivision

universe u s

variable {K D : Type u} [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K] [DivisionRing D] [Algebra K D]
  [FiniteDimensional K D] [Algebra.IsCentral K D]
variable {L : Type s} [Field L] [Algebra K L] (ι : L →ₐ[K] D)
variable {π : 𝒪[K]} (uniformizer : Dˣ)

local notation "d" => CentralSimple.reducedDegree K D
local notation "C" => SubfieldIntegerRing K D ι
local notation "vD" => localReducedNormValuation K D
local notation "w" => valuation K (π : K)

private theorem subfield_value_zpow (hL : IsUnramifiedSubfieldOfReducedDegree K D ι)
    (hπ : Irreducible π) {a : L} (ha : a ≠ 0) :
    ∃ n : ℤ, vD (ι a) = w ^ ((d : ℤ) * n) := by
  let : IsLocalHom (algebraMap 𝒪[K] C) := subfieldIntegerAlgebra_isLocalHom ι
  let : Module.Finite 𝒪[K] C := hL.2.1
  let : IsNoetherianRing C := IsNoetherianRing.of_finite 𝒪[K] C
  let : Algebra.Etale 𝒪[K] C := hL.2.2.1
  let : IsFractionRing C L := (Valuation.integer.integers
    (localDivisionSubfieldValuation K D ι)).isFractionRing
  have hmax : IsLocalRing.maximalIdeal C = Ideal.span {algebraMap 𝒪[K] C π} := by
    rw [← Algebra.FormallyUnramified.map_maximalIdeal (R := 𝒪[K]) (S := C),
      hπ.maximalIdeal_eq, Ideal.map_span, Set.image_singleton]
  have hπC : algebraMap 𝒪[K] C π ≠ 0 := by
    intro hh
    have hh' : algebraMap K L (π : K) = 0 := congrArg Subtype.val hh
    exact (map_ne_zero (algebraMap K L)).mpr (fun h => hπ.ne_zero (Subtype.ext h)) hh'
  have hnotField : ¬IsField C := by
    rw [IsLocalRing.isField_iff_maximalIdeal_eq, hmax, Ideal.span_singleton_eq_bot]
    exact hπC
  have hprincipal : (IsLocalRing.maximalIdeal C).IsPrincipal := by
    rw [hmax]
    exact ⟨⟨_, rfl⟩⟩
  let : IsDiscreteValuationRing C := ((IsDiscreteValuationRing.TFAE C hnotField).out 5 1).mp hprincipal
  have hπ' := IsDiscreteValuationRing.irreducible_of_span_eq_maximalIdeal _ hπC hmax
  obtain ⟨n, u, hu⟩ := IsDiscreteValuationRing.exists_units_eq_smul_zpow_of_irreducible hπ' ha
  have hvu : vD (ι ((u : C) : L)) = 1 :=
    (DivisionValuation.isUnit_iff_value_eq_one _ _).mp u.isUnit
  refine ⟨n, ?_⟩
  rw [hu]
  change vD (ι (((u : C) : L) * (algebraMap K L (π : K)) ^ n)) = _
  rw [map_mul, map_mul, hvu, one_mul, map_zpow₀, map_zpow₀, ι.commutes,
    localReducedNormValuation_algebraMap, ← zpow_natCast, ← zpow_mul]

private theorem uniformizer_value
    (hUniformizer : (uniformizer : D) ^ d = algebraMap K D (π : K)) :
    vD (uniformizer : D) = w := by
  apply (pow_left_inj₀ zero_le zero_le (CentralSimple.reducedDegree_pos K D).ne').mp
  rw [← map_pow, hUniformizer, localReducedNormValuation_algebraMap]

private theorem cyclicMonomial_value
    (hUniformizer : (uniformizer : D) ^ d = algebraMap K D (π : K))
    {a : L} {n : ℤ} (ha : vD (ι a) = w ^ ((d : ℤ) * n)) (i : Fin d) :
    vD (ι a * (uniformizer : D) ^ i.val) = w ^ ((d : ℤ) * n + (i.val : ℤ)) := by
  have hw : w ≠ 0 := by
    rw [← uniformizer_value uniformizer hUniformizer]
    exact (map_ne_zero _).mpr uniformizer.ne_zero
  rw [map_mul, map_pow, ha, uniformizer_value uniformizer hUniformizer, zpow_add₀ hw,
    zpow_natCast]

/-- Evaluate a tuple of field coefficients on the consecutive powers of the uniformizer. -/
def drinfeldCyclicExpansion : (Fin d → L) →ₗ[K] D where
  toFun a := ∑ i, ι (a i) * (uniformizer : D) ^ i.val
  map_add' a b := by simp only [Pi.add_apply, map_add, add_mul, Finset.sum_add_distrib]
  map_smul' r a := by simp only [Pi.smul_apply, map_smul, smul_mul_assoc, Finset.smul_sum,
    RingHom.id_apply]

private theorem drinfeldCyclicExpansion_dominant
    (hL : IsUnramifiedSubfieldOfReducedDegree K D ι) (hπ : Irreducible π)
    (hUniformizer : (uniformizer : D) ^ d = algebraMap K D (π : K))
    {a : Fin d → L} (ha : a ≠ 0) :
    ∃ i, a i ≠ 0 ∧
      vD (drinfeldCyclicExpansion ι uniformizer a) = vD (ι (a i) * (uniformizer : D) ^ i.val) ∧
      ∀ k, vD (ι (a k) * (uniformizer : D) ^ k.val) ≤ vD (ι (a i) * (uniformizer : D) ^ i.val) := by
  classical
  let t (i : Fin d) := ι (a i) * (uniformizer : D) ^ i.val
  have hw : 0 < w := by
    rw [← uniformizer_value uniformizer hUniformizer]
    exact pos_iff_ne_zero.mpr ((map_ne_zero _).mpr uniformizer.ne_zero)
  have hwlt : w < 1 := Valuation.integer.v_irreducible_lt_one hπ
  have hnz : ∃ k, a k ≠ 0 := by
    by_contra! h
    exact ha (funext h)
  obtain ⟨k, hk⟩ := hnz
  obtain ⟨i, hi, hmax⟩ := Finset.exists_max_image Finset.univ (fun j => vD (t j))
    ⟨k, Finset.mem_univ k⟩
  have ht (j : Fin d) (hj : a j ≠ 0) : 0 < vD (t j) :=
    pos_iff_ne_zero.mpr ((map_ne_zero _).mpr (mul_ne_zero ((map_ne_zero ι).mpr hj)
      (pow_ne_zero _ uniformizer.ne_zero)))
  have hi' : a i ≠ 0 := by
    intro he
    have h := (ht k hk).trans_le (hmax k (Finset.mem_univ k))
    simp only [t, he, map_zero, zero_mul, lt_self_iff_false] at h
  refine ⟨i, hi', ?_, fun j => hmax j (Finset.mem_univ j)⟩
  change vD (∑ j, t j) = vD (t i)
  apply Valuation.map_sum_eq_of_lt vD hi
  intro j hj
  have hne : j ≠ i := by simpa using (Finset.mem_sdiff.mp hj).2
  by_cases hj' : a j = 0
  · have hzero : vD (t j) = 0 := by simp [t, hj']
    rw [hzero]
    exact ht i hi'
  apply (hmax j (Finset.mem_univ j)).lt_of_ne
  obtain ⟨n, hn⟩ := subfield_value_zpow ι hL hπ (show a j ≠ 0 from hj')
  obtain ⟨m, hm⟩ := subfield_value_zpow ι hL hπ hi'
  intro h
  change vD (ι (a j) * (uniformizer : D) ^ j.val) =
    vD (ι (a i) * (uniformizer : D) ^ i.val) at h
  rw [cyclicMonomial_value ι uniformizer hUniformizer hn j,
    cyclicMonomial_value ι uniformizer hUniformizer hm i] at h
  have he := (zpow_right_injective₀ hw hwlt.ne) h
  have hmod := congrArg (fun x : ℤ => x % (d : ℤ)) he
  have hlt (l : Fin d) : (l.val : ℤ) < (d : ℤ) := by exact_mod_cast l.isLt
  rw [add_comm ((d : ℤ) * n), add_comm ((d : ℤ) * m), Int.add_mul_emod_self_left,
    Int.add_mul_emod_self_left, Int.emod_eq_of_lt (by positivity) (hlt j),
    Int.emod_eq_of_lt (by positivity) (hlt i)] at hmod
  exact hne (Fin.ext (by exact_mod_cast hmod))

/-- The powers below the reduced degree give the actual cyclic coordinates over the field. -/
def drinfeldCyclicFieldEquiv (hL : IsUnramifiedSubfieldOfReducedDegree K D ι)
    (hπ : Irreducible π)
    (hUniformizer : (uniformizer : D) ^ d = algebraMap K D (π : K)) :
    (Fin d → L) ≃ₗ[K] D := by
  let : FiniteDimensional K L := hL.1
  refine LinearEquiv.ofInjectiveOfFinrankEq (drinfeldCyclicExpansion ι uniformizer) ?_ ?_
  · apply (injective_iff_map_eq_zero _).2
    intro a ha
    by_contra h
    obtain ⟨i, hi, hv, _⟩ := drinfeldCyclicExpansion_dominant ι uniformizer hL hπ hUniformizer h
    rw [ha, map_zero] at hv
    exact ((map_ne_zero _).mpr (mul_ne_zero ((map_ne_zero ι).mpr hi)
      (pow_ne_zero _ uniformizer.ne_zero))) hv.symm
  · rw [Module.finrank_pi_fintype, CentralSimple.finrank_eq_reducedDegree_mul_self K D]
    simp [hL.2.2.2]

private theorem cyclicExpansion_coefficients_integral
    (hL : IsUnramifiedSubfieldOfReducedDegree K D ι) (hπ : Irreducible π)
    (hUniformizer : (uniformizer : D) ^ d = algebraMap K D (π : K))
    (a : Fin d → L) (ha : vD (drinfeldCyclicExpansion ι uniformizer a) ≤ 1) (i : Fin d) :
    vD (ι (a i)) ≤ 1 := by
  by_cases hi : a i = 0
  · simp [hi]
  have hnonzero : a ≠ 0 := fun he => hi (congrFun he i)
  obtain ⟨j, _, hj, hmax⟩ :=
    drinfeldCyclicExpansion_dominant ι uniformizer hL hπ hUniformizer hnonzero
  have hbound := (hmax i).trans (hj ▸ ha)
  obtain ⟨n, hn⟩ := subfield_value_zpow ι hL hπ hi
  rw [cyclicMonomial_value ι uniformizer hUniformizer hn i] at hbound
  have hw : 0 < w := by
    rw [← uniformizer_value uniformizer hUniformizer]
    exact pos_iff_ne_zero.mpr ((map_ne_zero _).mpr uniformizer.ne_zero)
  have hwlt : w < 1 := Valuation.integer.v_irreducible_lt_one hπ
  have he := (zpow_le_one_iff_right_of_lt_one₀ hw hwlt).mp hbound
  have hd : 0 ≤ (d : ℤ) := by positivity
  have hi' : (i.val : ℤ) < (d : ℤ) := by exact_mod_cast i.isLt
  have hn' : 0 ≤ n := by
    by_contra! hneg
    have hmul := mul_le_mul_of_nonneg_left (show n ≤ -1 by omega) hd
    rw [mul_neg_one] at hmul
    omega
  rw [hn]
  exact zpow_le_one₀ hw hwlt.le (mul_nonneg hd hn')

private def drinfeldIntegralCyclicSum
    (hUniformizer : (uniformizer : D) ^ d = algebraMap K D (π : K)) :
    (Fin d → C) →ₗ[𝒪[K]] IntegerRing K D where
  toFun a := ∑ i, subfieldIntegerInclusion K D ι (a i) *
    drinfeldIntegralUniformizer uniformizer hUniformizer ^ i.val
  map_add' a b := by simp only [Pi.add_apply, map_add, add_mul, Finset.sum_add_distrib]
  map_smul' r a := by simp only [Pi.smul_apply, map_smul, smul_mul_assoc, Finset.smul_sum,
    RingHom.id_apply]

private theorem drinfeldIntegralCyclicSum_coe
    (hUniformizer : (uniformizer : D) ^ d = algebraMap K D (π : K)) (a : Fin d → C) :
    (drinfeldIntegralCyclicSum ι uniformizer hUniformizer a : D) =
      drinfeldCyclicExpansion ι uniformizer (fun i => (a i : L)) := by
  change (localReducedNormValuation K D).integer.subtype
      (∑ i, subfieldIntegerInclusion K D ι (a i) *
        drinfeldIntegralUniformizer uniformizer hUniformizer ^ i.val) = _
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [map_mul, map_pow]
  rfl

/-- The actual division order has unique integral coefficients in the cyclic expansion. -/
def drinfeldIntegralCyclicEquiv (hL : IsUnramifiedSubfieldOfReducedDegree K D ι)
    (hπ : Irreducible π)
    (hUniformizer : (uniformizer : D) ^ d = algebraMap K D (π : K)) :
    (Fin d → C) ≃ₗ[𝒪[K]] IntegerRing K D := by
  let e := drinfeldCyclicFieldEquiv ι uniformizer hL hπ hUniformizer
  refine LinearEquiv.ofBijective (drinfeldIntegralCyclicSum ι uniformizer hUniformizer) ⟨?_, ?_⟩
  · intro a b h
    have h' := congrArg Subtype.val h
    rw [drinfeldIntegralCyclicSum_coe, drinfeldIntegralCyclicSum_coe] at h'
    have hcoeff : (fun i => (a i : L)) = fun i => (b i : L) := e.injective h'
    exact funext fun i => Subtype.ext (congrFun hcoeff i)
  · intro b
    let a := e.symm (b : D)
    have ha : drinfeldCyclicExpansion ι uniformizer a = (b : D) := e.apply_symm_apply _
    have hb : vD (drinfeldCyclicExpansion ι uniformizer a) ≤ 1 := by rw [ha]; exact b.prop
    let c (i : Fin d) : C := ⟨a i, cyclicExpansion_coefficients_integral
      ι uniformizer hL hπ hUniformizer a hb i⟩
    refine ⟨c, Subtype.ext ?_⟩
    rw [drinfeldIntegralCyclicSum_coe]
    exact ha

@[simp]
theorem drinfeldIntegralCyclicEquiv_apply (hL : IsUnramifiedSubfieldOfReducedDegree K D ι)
    (hπ : Irreducible π)
    (hUniformizer : (uniformizer : D) ^ d = algebraMap K D (π : K)) (a : Fin d → C) :
    drinfeldIntegralCyclicEquiv ι uniformizer hL hπ hUniformizer a =
      ∑ i, subfieldIntegerInclusion K D ι (a i) *
        drinfeldIntegralUniformizer uniformizer hUniformizer ^ i.val := rfl

/-- The coefficient inclusion and the division uniformizer determine a ring homomorphism. -/
theorem drinfeldOrder_ringHom_ext (hL : IsUnramifiedSubfieldOfReducedDegree K D ι)
    (hπ : Irreducible π)
    (hUniformizer : (uniformizer : D) ^ d = algebraMap K D (π : K))
    {A : Type*} [Ring A] {f g : IntegerRing K D →+* A}
    (hC : ∀ a : C, f (subfieldIntegerInclusion K D ι a) = g (subfieldIntegerInclusion K D ι a))
    (hUniformizerMap : f (drinfeldIntegralUniformizer uniformizer hUniformizer) =
      g (drinfeldIntegralUniformizer uniformizer hUniformizer)) : f = g := by
  apply RingHom.ext
  intro a
  obtain ⟨c, rfl⟩ := (drinfeldIntegralCyclicEquiv ι uniformizer hL hπ hUniformizer).surjective a
  simp only [drinfeldIntegralCyclicEquiv_apply, map_sum, map_mul, map_pow, hC, hUniformizerMap]

end Langlands.FormalGroup.LocalDivision
