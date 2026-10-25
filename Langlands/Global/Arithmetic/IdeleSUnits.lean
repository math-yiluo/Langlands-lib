import Langlands.ClassField.Global.IdeleDivisor
import Langlands.Global.Arithmetic.SUnitIndex
import Mathlib.NumberTheory.NumberField.ClassNumber
import Mathlib.RingTheory.DedekindDomain.Factorization

/-! # Ideles that are units outside a finite set of places -/

noncomputable section

namespace Langlands.Global.Arithmetic.IdeleSUnits

open NumberField IsDedekindDomain IsDedekindDomain.HeightOneSpectrum
open Langlands.ClassField.Global Langlands.Global.Arithmetic.SUnitIndex
open scoped NumberField nonZeroDivisors

variable {K : Type*} [Field K] [NumberField K]

/-- The valuation exponent `J_K → ℤ` of an idele at a finite place `v` (multiplicatively). -/
def ideleExponent (v : HeightOneSpectrum (𝓞 K)) : IdeleGroup (𝓞 K) K →* Multiplicative ℤ :=
  (unitsExponent v).comp (ideleCoordinate v)

theorem ideleExponent_eq_one_iff (v : HeightOneSpectrum (𝓞 K)) (x : IdeleGroup (𝓞 K) K) :
    ideleExponent v x = 1 ↔ Valued.v (ideleCoordinate v x : v.adicCompletion K) = 1 :=
  unitsExponent_eq_one_iff v _

theorem exp_ideleExponent_unitEmbedding (v : HeightOneSpectrum (𝓞 K)) (a : Kˣ) :
    WithZero.exp (Multiplicative.toAdd (ideleExponent v (IdeleGroup.unitEmbedding (𝓞 K) K a))) =
      v.valuation K (a : K) := by
  change WithZero.exp (Multiplicative.toAdd (unitsExponent v (ideleCoordinate v _))) = _
  rw [← valued_units]
  exact valuedAdicCompletion_eq_valuation' v (a : K)

theorem ideleExponent_unitEmbedding_eq_one_iff (v : HeightOneSpectrum (𝓞 K)) (a : Kˣ) :
    ideleExponent v (IdeleGroup.unitEmbedding (𝓞 K) K a) = 1 ↔ v.valuation K (a : K) = 1 := by
  rw [← exp_ideleExponent_unitEmbedding, ← WithZero.exp_zero, WithZero.exp_injective.eq_iff]
  rfl

variable (K) in
/-- The ideles whose coordinates are valuation units at every finite place outside the finite
set `S` of finite places. The infinite coordinates are arbitrary. -/
def sUnitIdeles (S : Finset (HeightOneSpectrum (𝓞 K))) : Subgroup (IdeleGroup (𝓞 K) K) :=
  ⨅ (v) (_ : v ∉ S), (ideleExponent v).ker

theorem mem_sUnitIdeles_iff {S : Finset (HeightOneSpectrum (𝓞 K))} {x : IdeleGroup (𝓞 K) K} :
    x ∈ sUnitIdeles K S ↔ ∀ v ∉ S, ideleExponent v x = 1 := by
  simp only [sUnitIdeles, Subgroup.mem_iInf, MonoidHom.mem_ker]

theorem sUnitIdeles_mono {S T : Finset (HeightOneSpectrum (𝓞 K))} (h : S ⊆ T) :
    sUnitIdeles K S ≤ sUnitIdeles K T := fun _ hx =>
  mem_sUnitIdeles_iff.2 fun v hv => mem_sUnitIdeles_iff.1 hx v (fun hS => hv (h hS))

/-- A principal idele lies in `sUnitIdeles K S` exactly when it comes from an `S`-unit. -/
theorem unitEmbedding_mem_sUnitIdeles_iff {S : Finset (HeightOneSpectrum (𝓞 K))} (a : Kˣ) :
    IdeleGroup.unitEmbedding (𝓞 K) K a ∈ sUnitIdeles K S ↔ a ∈ sUnits K S := by
  rw [mem_sUnitIdeles_iff]
  simp only [ideleExponent_unitEmbedding_eq_one_iff]
  rfl

theorem unitEmbedding_injective :
    Function.Injective (IdeleGroup.unitEmbedding (𝓞 K) K) := fun _ _ h =>
  Units.ext (AdeleRing.algebraMap_injective (𝓞 K) K (congrArg Units.val h))

variable (K) in
/-- The `S`-units as ideles in `sUnitIdeles K S`. -/
def sUnitsToIdeles (S : Finset (HeightOneSpectrum (𝓞 K))) : sUnits K S →* sUnitIdeles K S :=
  ((IdeleGroup.unitEmbedding (𝓞 K) K).comp (sUnits K S).subtype).codRestrict _ fun a =>
    (unitEmbedding_mem_sUnitIdeles_iff a.1).2 a.2

theorem sUnitsToIdeles_injective (S : Finset (HeightOneSpectrum (𝓞 K))) :
    Function.Injective (sUnitsToIdeles K S) := fun _ _ h =>
  Subtype.ext (unitEmbedding_injective (congrArg Subtype.val h))

/-- The principal ideles in `sUnitIdeles K S` are the images of the `S`-units. -/
theorem range_sUnitsToIdeles (S : Finset (HeightOneSpectrum (𝓞 K))) :
    (sUnitsToIdeles K S).range =
      (IdeleGroup.principalSubgroup (𝓞 K) K).subgroupOf (sUnitIdeles K S) := by
  ext x
  rw [Subgroup.mem_subgroupOf]
  constructor
  · rintro ⟨a, rfl⟩
    exact ⟨a.1, rfl⟩
  · rintro ⟨a, ha⟩
    have hmem : a ∈ sUnits K S := (unitEmbedding_mem_sUnitIdeles_iff a).1 (ha ▸ x.2)
    exact ⟨⟨a, hmem⟩, Subtype.ext ha⟩

section Generation

variable (K) in
/-- Every finite place `v ∉ S` has a *global uniformizer*: an element `π ∈ Kˣ` with exponent
`-1` at `v` (valuation `exp (-1)`) that is a unit at every other finite place outside `S`.
This holds as soon as the classes of the places in `S` generate the class group. -/
def HasGlobalUniformizers (S : Finset (HeightOneSpectrum (𝓞 K))) : Prop :=
  ∀ v ∉ S, ∃ π : Kˣ,
    Multiplicative.toAdd (ideleExponent v (IdeleGroup.unitEmbedding (𝓞 K) K π)) = -1 ∧
      ∀ w ∉ S, w ≠ v → ideleExponent w (IdeleGroup.unitEmbedding (𝓞 K) K π) = 1

theorem HasGlobalUniformizers.mono {S T : Finset (HeightOneSpectrum (𝓞 K))}
    (hS : HasGlobalUniformizers K S) (h : S ⊆ T) : HasGlobalUniformizers K T := by
  intro v hv
  obtain ⟨π, h1, h2⟩ := hS v (fun h' => hv (h h'))
  exact ⟨π, h1, fun w hw hwv => h2 w (fun h' => hw (h h')) hwv⟩

/-- The exponent of a nonzero algebraic integer is read off from its `v`-adic valuation. -/
theorem exp_ideleExponent_algebraMap (v : HeightOneSpectrum (𝓞 K)) {r : 𝓞 K}
    (hr : (algebraMap (𝓞 K) K r) ≠ 0) :
    WithZero.exp (Multiplicative.toAdd
      (ideleExponent v (IdeleGroup.unitEmbedding (𝓞 K) K (Units.mk0 _ hr)))) =
      v.intValuation r := by
  rw [exp_ideleExponent_unitEmbedding, Units.val_mk0, valuation_of_algebraMap]

variable (K) in
/-- Every finite set of finite places is contained in a finite set with global uniformizers.
Choose an integral ideal `I_c` in every ideal class `c` and add the places dividing some `I_c`.
For `v` outside, `v · I_c` is principal for `c = [v]⁻¹`; a generator is a global uniformizer. -/
theorem exists_hasGlobalUniformizers (S₀ : Finset (HeightOneSpectrum (𝓞 K))) :
    ∃ S : Finset (HeightOneSpectrum (𝓞 K)), S₀ ⊆ S ∧ HasGlobalUniformizers K S := by
  classical
  choose I hI using (ClassGroup.mk0_surjective (R := 𝓞 K))
  have hI0 : ∀ c, (I c : Ideal (𝓞 K)) ≠ 0 := fun c => nonZeroDivisors.coe_ne_zero (I c)
  have hfin : ∀ c, {v : HeightOneSpectrum (𝓞 K) | v.asIdeal ∣ (I c : Ideal (𝓞 K))}.Finite :=
    fun c => Ideal.finite_factors (hI0 c)
  let S : Finset (HeightOneSpectrum (𝓞 K)) :=
    S₀ ∪ Finset.univ.biUnion fun c => (hfin c).toFinset
  have hS : ∀ (c) (w : HeightOneSpectrum (𝓞 K)), w.asIdeal ∣ (I c : Ideal (𝓞 K)) → w ∈ S :=
    fun c w hw => Finset.mem_union_right _
      (Finset.mem_biUnion.2 ⟨c, Finset.mem_univ _, (hfin c).mem_toFinset.2 hw⟩)
  refine ⟨S, Finset.subset_union_left, ?_⟩
  intro v hv
  have hv0 : v.asIdeal ∈ (Ideal (𝓞 K))⁰ := mem_nonZeroDivisors_of_ne_zero v.ne_bot
  set c := (ClassGroup.mk0 ⟨v.asIdeal, hv0⟩)⁻¹ with hc
  have hvI : v.asIdeal * (I c : Ideal (𝓞 K)) ∈ (Ideal (𝓞 K))⁰ :=
    mul_mem_nonZeroDivisors.2 ⟨hv0, (I c).2⟩
  have hprin : (v.asIdeal * (I c : Ideal (𝓞 K))).IsPrincipal := by
    rw [← ClassGroup.mk0_eq_one_iff hvI]
    have : (⟨v.asIdeal * (I c : Ideal (𝓞 K)), hvI⟩ : (Ideal (𝓞 K))⁰) = ⟨v.asIdeal, hv0⟩ * I c :=
      rfl
    rw [this, map_mul, hI, hc, mul_inv_cancel]
  obtain ⟨π, hπ⟩ := hprin.principal
  have hπ' : v.asIdeal * (I c : Ideal (𝓞 K)) = Ideal.span {π} := hπ
  have hπ0 : π ≠ 0 := by
    rintro rfl
    rw [Ideal.span_singleton_eq_bot.2 rfl] at hπ'
    exact nonZeroDivisors.coe_ne_zero ⟨_, hvI⟩ hπ'
  have hπK : algebraMap (𝓞 K) K π ≠ 0 :=
    (map_ne_zero_iff _ (FaithfulSMul.algebraMap_injective (𝓞 K) K)).2 hπ0
  refine ⟨Units.mk0 _ hπK, ?_, ?_⟩
  · -- exponent `-1` at `v`
    set m := Multiplicative.toAdd
      (ideleExponent v (IdeleGroup.unitEmbedding (𝓞 K) K (Units.mk0 _ hπK)))
    have hm := exp_ideleExponent_algebraMap v hπK
    have h1 : v.intValuation π ≤ WithZero.exp (-((1 : ℕ) : ℤ)) := by
      rw [intValuation_le_pow_iff_dvd, pow_one, ← hπ']
      exact dvd_mul_right _ _
    have h2 : ¬ v.intValuation π ≤ WithZero.exp (-((2 : ℕ) : ℤ)) := by
      rw [intValuation_le_pow_iff_dvd, ← hπ', pow_two]
      intro h
      rw [mul_dvd_mul_iff_left v.ne_bot] at h
      exact hv (hS c v h)
    rw [← hm, WithZero.exp_le_exp] at h1 h2
    push_cast at h1 h2
    omega
  · intro w hw hwv
    rw [ideleExponent_unitEmbedding_eq_one_iff, Units.val_mk0, valuation_of_algebraMap,
      intValuation_eq_one_iff]
    intro hmem
    have hle : v.asIdeal * (I c : Ideal (𝓞 K)) ≤ w.asIdeal := by
      rw [hπ', Ideal.span_le, Set.singleton_subset_iff]
      exact hmem
    rcases (Ideal.IsPrime.mul_le w.isPrime).1 hle with h | h
    · exact hwv (HeightOneSpectrum.ext (v.isMaximal.eq_of_le w.isPrime.ne_top h).symm)
    · exact hw (hS c w (Ideal.dvd_iff_le.2 h))

/-- **Ideles modulo `S`-unit ideles.** If `S` has global uniformizers, every idele is a principal
idele times an idele that is a unit at every finite place outside `S`. -/
theorem principal_sup_sUnitIdeles {S : Finset (HeightOneSpectrum (𝓞 K))}
    (hS : HasGlobalUniformizers K S) :
    IdeleGroup.principalSubgroup (𝓞 K) K ⊔ sUnitIdeles K S = ⊤ := by
  classical
  choose π hπv hπw using hS
  rw [eq_top_iff]
  intro y _
  let π' : HeightOneSpectrum (𝓞 K) → Kˣ := fun v => if h : v ∈ S then 1 else π v h
  have hsupp : (Function.mulSupport fun v => ideleExponent v y).Finite := by
    apply (ideleOrder_finite_support y).subset
    intro v hv h0
    apply hv
    change -Multiplicative.toAdd (ideleExponent v y) = 0 at h0
    rw [neg_eq_zero] at h0
    exact h0
  set T := hsupp.toFinset
  let n : HeightOneSpectrum (𝓞 K) → ℤ := fun v => Multiplicative.toAdd (ideleExponent v y)
  let a : Kˣ := ∏ v ∈ T, π' v ^ n v
  have hz : y * IdeleGroup.unitEmbedding (𝓞 K) K a ∈ sUnitIdeles K S := by
    rw [mem_sUnitIdeles_iff]
    intro w hw
    rw [map_mul, map_prod, map_prod]
    simp only [map_zpow]
    by_cases hwT : w ∈ T
    · rw [Finset.prod_eq_single w]
      · have h1 : ideleExponent w (IdeleGroup.unitEmbedding (𝓞 K) K (π' w)) =
            Multiplicative.ofAdd (-1) := by
          simp only [π', hw, ↓reduceDIte]
          exact (hπv w hw).symm ▸ rfl
        rw [h1, ← ofAdd_zsmul]
        apply Multiplicative.toAdd.injective
        simp [n]
      · intro v _ hvw
        have h1 : ideleExponent w (IdeleGroup.unitEmbedding (𝓞 K) K (π' v)) = 1 := by
          by_cases hvS : v ∈ S
          · simp only [π', hvS, ↓reduceDIte, map_one]
          · simp only [π', hvS, ↓reduceDIte]
            exact hπw v hvS w hw (Ne.symm hvw)
        rw [h1, one_zpow]
      · intro h; exact absurd hwT h
    · have hy : ideleExponent w y = 1 := by
        by_contra h
        exact hwT (hsupp.mem_toFinset.2 h)
      rw [hy, one_mul]
      apply Finset.prod_eq_one
      intro v hv
      have hvw : v ≠ w := fun h => hwT (h ▸ hv)
      have h1 : ideleExponent w (IdeleGroup.unitEmbedding (𝓞 K) K (π' v)) = 1 := by
        by_cases hvS : v ∈ S
        · simp only [π', hvS, ↓reduceDIte, map_one]
        · simp only [π', hvS, ↓reduceDIte]
          exact hπw v hvS w hw (Ne.symm hvw)
      rw [h1, one_zpow]
  have : y = IdeleGroup.unitEmbedding (𝓞 K) K a⁻¹ *
      (y * IdeleGroup.unitEmbedding (𝓞 K) K a) := by
    rw [map_inv, mul_comm y, inv_mul_cancel_left]
  rw [this]
  exact Subgroup.mul_mem_sup ⟨a⁻¹, rfl⟩ hz

end Generation

end Langlands.Global.Arithmetic.IdeleSUnits
