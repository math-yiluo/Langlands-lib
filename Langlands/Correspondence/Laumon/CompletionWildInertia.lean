import Langlands.Correspondence.Laumon.CompletionLowerGroups
import Langlands.LocalFactor.Ramification.Herbrand.LocalAbsoluteImageProof

/-!
# Wild inertia of `k((t))` and the roots of the uniformizer

For a finite field `k` of characteristic `p`, an automorphism `σ` of the separable closure of
`LaurentSeries k` lies in the Library's wild inertia `localWildInertia` exactly when it lies in
the Library's inertia and fixes every root `ϖ` of `ϖ ^ N = t` with `p ∤ N`. With restriction a
homeomorphism, this describes the image of wild inertia in the Galois group of the end field.
-/

noncomputable section

universe u

namespace Langlands.Henniart.Laumon

attribute [local instance] Langlands.LocalField.Laurent.valuativeRel

open IsLocalRing ValuativeRel
open Langlands.LocalGalois Langlands.LocalGalois.SepClosed Langlands.Ramification.Local
open scoped NNReal WithZero

variable (k : Type u) [Field k] [Finite k]

local instance : NontriviallyNormedField (LaurentSeries k) := localNormedField (LaurentSeries k)
local instance : IsUltrametricDist (LaurentSeries k) := localNormedField_ultrametric _
local instance : CompleteSpace (LaurentSeries k) := localNormedField_complete _
local instance : Finite (ResidueField (baseIntegers (LaurentSeries k))) := localResidue_finite _

local notation "X" => LaurentSeries k
local notation "Ωx" => SeparableClosure (LaurentSeries k)
local notation "𝔸" => closureIntegers (LaurentSeries k) (SeparableClosure (LaurentSeries k))
local notation "νx" => closureValuation (LaurentSeries k) (SeparableClosure (LaurentSeries k))

section Basic

/-- The constants `k → SeparableClosure (LaurentSeries k)`. -/
def closureConstantHom : k →+* Ωx :=
  (algebraMap (endGenericClosure k) Ωx).comp ((algebraMap (endField k) (endGenericClosure k)).comp
    ((endRing k).subtype.comp (endConstantHom k)))

omit [Finite k] in
/-- The separable closure of `k((t))` has the characteristic of `k`. -/
theorem closure_charP : CharP Ωx (ringChar k) :=
  charP_of_injective_ringHom (closureConstantHom k).injective (ringChar k)

/-- An integer prime to `p` is a unit in the integers of the separable closure. -/
theorem natCast_isUnit {N : ℕ} (hN : ¬ ringChar k ∣ N) : IsUnit (N : 𝔸) := by
  let := Fintype.ofFinite k
  have hc : (N : k) ≠ 0 := fun h => hN ((CharP.cast_eq_zero_iff k (ringChar k) N).mp h)
  have h1 := FiniteField.pow_card_sub_one_eq_one (N : k) hc
  have hq : Fintype.card k - 1 ≠ 0 := by
    have := Fintype.one_lt_card (α := k)
    omega
  have h2 : (N : 𝔸) ^ (Fintype.card k - 1) = 1 := by
    apply Subtype.ext
    have := congrArg (closureConstantHom k) h1
    rw [map_pow, map_natCast, map_one] at this
    simpa using this
  exact IsUnit.of_pow_eq_one h2 hq

/-- The uniformizer `t` of the end trait, in the separable closure of `k((t))`. -/
abbrev closureUniformizer : Ωx :=
  ((algebraMap (endField k) (endGenericClosure k)
    ((endUniformizer k .zero : endRing k) : endField k) : endGenericClosure k) : Ωx)

omit [Finite k] in
theorem closureUniformizer_eq :
    closureUniformizer k =
      algebraMap X Ωx (HahnSeries.ofPowerSeries ℤ k PowerSeries.X) := by
  change algebraMap X Ωx (algebraMap (RatFunc k) X RatFunc.X) = _
  rw [algebraMap_ratFunc_X]

omit [Finite k] in
theorem closureUniformizer_ne_zero : closureUniformizer k ≠ 0 := by
  rw [closureUniformizer_eq, ne_eq, map_eq_zero_iff _ (algebraMap X Ωx).injective]
  intro h
  have := congrArg (fun f : X => f.coeff 1) h
  simp at this

theorem closureUniformizer_lt_one : νx (closureUniformizer k) < 1 := by
  rw [closureUniformizer_eq, Valuation.HasExtension.val_map_lt_one_iff (vR := valuation X)]
  have h := LaurentSeries.valuation_X_pow (K := k) 1
  rw [pow_one] at h
  have hlt : (Valued.v : Valuation X ℤᵐ⁰) (HahnSeries.ofPowerSeries ℤ k PowerSeries.X) <
      (Valued.v : Valuation X ℤᵐ⁰) 1 := by
    rw [map_one]
    rw [h]
    exact WithZero.exp_lt_one_iff.mpr (by norm_num)
  rw [← map_one (valuation X), ← not_le, compatible_le_iff (Valued.v : Valuation X ℤᵐ⁰),
    not_le]
  exact hlt

omit [Finite k] in
theorem closureUniformizer_mem (L : FiniteGaloisIntermediateField X Ωx) :
    closureUniformizer k ∈ L.toIntermediateField := by
  rw [closureUniformizer_eq]
  exact L.toIntermediateField.algebraMap_mem _

omit [Finite k] in
theorem closureUniformizer_map (σ : Gal(Ωx/X)) : σ (closureUniformizer k) = closureUniformizer k := by
  rw [closureUniformizer_eq]
  exact σ.commutes _

omit [Finite k] in
/-- A root in the separable closure of `ϖ ^ N = t`, `N` prime to `p`, is separable over the end
field. -/
theorem mem_endGenericClosure_of_pow_eq_closureUniformizer {ϖ : Ωx} {N : ℕ}
    (hN : (N : Ωx) ≠ 0) (hϖ : ϖ ^ N = closureUniformizer k) : ϖ ∈ endGenericClosure k := by
  rw [mem_separableClosure_iff]
  have hNK : (N : endField k) ≠ 0 := fun h =>
    hN (by simpa only [map_natCast, map_zero] using congrArg (algebraMap (endField k) Ωx) h)
  have ht : ((endUniformizer k .zero : endRing k) : endField k) ≠ 0 := by
    intro h
    apply closureUniformizer_ne_zero k
    change ((algebraMap (endField k) (endGenericClosure k) _ : endGenericClosure k) : Ωx) = 0
    rw [h, map_zero, ZeroMemClass.coe_zero]
  have hsep := Polynomial.separable_X_pow_sub_C
    ((endUniformizer k .zero : endRing k) : endField k) hNK ht
  refine hsep.of_dvd (minpoly.dvd _ _ ?_)
  simp only [map_sub, map_pow, Polynomial.aeval_X, Polynomial.aeval_C, hϖ, sub_eq_zero]
  rfl

end Basic

section Inertia

omit [Finite k] in
theorem residue_eq_residue_iff_sub_mem {R : Type*} [CommRing R] [IsLocalRing R] (a b : R) :
    residue R a = residue R b ↔ a - b ∈ maximalIdeal R := by
  rw [← sub_eq_zero, ← map_sub, residue_eq_zero_iff]

/-- If `σ` lies in absolute inertia, then `σ x - x` lies in the maximal ideal for every
integral `x`. -/
theorem sub_lt_one_of_mem_absoluteInertia {σ : Gal(Ωx/X)} (hσ : σ ∈ absoluteInertia X Ωx)
    {x : Ωx} (hx : νx x ≤ 1) : νx (σ x - x) < 1 := by
  have h := (mem_inertia_iff X Ωx σ).mp hσ ⟨x, hx⟩
  rw [residue_eq_residue_iff_sub_mem, Separable.mem_maximalIdeal_iff_lt] at h
  exact h

/-- If `σ x - x` lies in the maximal ideal for every integral `x`, then `σ` lies in
absolute inertia. -/
theorem mem_absoluteInertia_of_sub_lt_one {σ : Gal(Ωx/X)}
    (h : ∀ x : Ωx, νx x ≤ 1 → νx (σ x - x) < 1) : σ ∈ absoluteInertia X Ωx := by
  change σ ∈ inertia X Ωx
  rw [mem_inertia_iff]
  intro x
  rw [residue_eq_residue_iff_sub_mem, Separable.mem_maximalIdeal_iff_lt]
  exact h x x.2

/-- Every integral element of a finite level is congruent to a constant lying in that level. -/
theorem exists_constant_mem_level (L : FiniteGaloisIntermediateField X Ωx) {x : Ωx}
    (hxL : x ∈ L.toIntermediateField) (hx : νx x ≤ 1) :
    ∃ a : endConstants k, ((a : endGenericClosure k) : Ωx) ∈ L.toIntermediateField ∧
      νx (x - ((a : endGenericClosure k) : Ωx)) < 1 := by
  obtain ⟨a, ha⟩ := constantsResidue_surjective k (residue 𝔸 ⟨x, hx⟩)
  refine ⟨a, ?_, ?_⟩
  · rw [← InfiniteGalois.fixedField_fixingSubgroup L.toIntermediateField,
      IntermediateField.mem_fixedField_iff]
    intro τ hτ
    have h1 := constantsResidue_map k τ a (restrictedConstant k τ a) rfl
    have hfix : integerAut X Ωx τ ⟨x, hx⟩ = ⟨x, hx⟩ :=
      Subtype.ext ((IntermediateField.mem_fixingSubgroup_iff _ _).mp hτ x hxL)
    rw [ha, residueHom_apply, hfix, ← ha] at h1
    have h2 := congrArg (fun c : endConstants k => ((c : endGenericClosure k) : Ωx))
      (constantsResidue_injective k h1)
    rw [← completionRestriction_apply]
    exact h2
  · rw [constantsResidue_apply, residue_eq_residue_iff_sub_mem,
      Separable.mem_maximalIdeal_iff_lt] at ha
    rw [← Valuation.map_neg, neg_sub]
    exact ha

end Inertia

section Wild

/-- The first lower ramification group of a finite level, read off `closureValuation` through an
element `π` of the level of maximal valuation `< 1`. -/
theorem mem_lowerRamificationGroup_one_iff (L : FiniteGaloisIntermediateField X Ωx) {π : L}
    (hπ1 : νx (π : Ωx) < 1) (hπ : ∀ y : L, νx (y : Ωx) < 1 → νx (y : Ωx) ≤ νx (π : Ωx))
    (σ : Gal(Ωx/X)) :
    absoluteFiniteRestriction X Ωx L σ ∈ lowerRamificationGroup (localTopologicalData X L) X 1 ↔
      ∀ x ∈ L.toIntermediateField, νx x ≤ 1 → νx (σ x - x) ≤ νx (π : Ωx) ^ 2 := by
  rw [mem_lowerRamificationGroup_iff_closureValuation hπ1 hπ]
  constructor
  · intro h x hxL hx
    have := h ⟨x, hxL⟩ hx
    rwa [AddSubgroupClass.coe_sub, absoluteFiniteRestriction_apply] at this
  · intro h x hx
    rw [AddSubgroupClass.coe_sub, absoluteFiniteRestriction_apply]
    exact h x x.2 hx

omit [Finite k] in
theorem apply_mem_level (L : FiniteGaloisIntermediateField X Ωx) (σ : Gal(Ωx/X)) {y : Ωx}
    (hy : y ∈ L.toIntermediateField) : σ y ∈ L.toIntermediateField := by
  have := (absoluteFiniteRestriction X Ωx L σ ⟨y, hy⟩).2
  rwa [absoluteFiniteRestriction_apply] at this

/-- Wild inertia fixes the `N`-th roots of `t`, `N` prime to `p`. -/
theorem fixes_root_of_forall_lower_one {σ : Gal(Ωx/X)}
    (h : ∀ L : FiniteGaloisIntermediateField X Ωx,
      absoluteFiniteRestriction X Ωx L σ ∈ lowerRamificationGroup (localTopologicalData X L) X 1)
    {N : ℕ} (hN : ¬ ringChar k ∣ N) {ϖ : Ωx} (hϖ : ϖ ^ N = closureUniformizer k) : σ ϖ = ϖ := by
  let L := FiniteGaloisIntermediateField.adjoin X ({ϖ} : Set Ωx)
  have hϖL : ϖ ∈ L.toIntermediateField :=
    FiniteGaloisIntermediateField.subset_adjoin X ({ϖ} : Set Ωx) (Set.mem_singleton ϖ)
  obtain ⟨π, hπ0, hπ1, hπ⟩ := exists_levelUniformizer X Ωx L
  have hcrit := (mem_lowerRamificationGroup_one_iff k L hπ1 hπ σ).mp (h L)
  have hN0 : N ≠ 0 := by
    rintro rfl
    exact hN (dvd_zero _)
  have hϖ0 : ϖ ≠ 0 := by
    rintro rfl
    rw [zero_pow hN0] at hϖ
    exact closureUniformizer_ne_zero k hϖ.symm
  have hϖ1 : νx ϖ < 1 := by
    have ht := closureUniformizer_lt_one k
    rw [← hϖ, map_pow] at ht
    exact (pow_lt_one_iff_of_nonneg zero_le hN0).mp ht
  have hπ0' : (π : Ωx) ≠ 0 := by
    intro h0
    rw [h0, map_zero] at hπ0
    exact lt_irrefl _ hπ0
  obtain ⟨n, hn⟩ := exists_closureValuation_eq_pow hπ1 hπ (y := ⟨ϖ, hϖL⟩)
    (fun h0 => hϖ0 (congrArg Subtype.val h0)) hϖ1.le
  have hv0 : νx ϖ ≠ 0 := (Valuation.ne_zero_iff _).mpr hϖ0
  have hϖv0 : 0 < νx ϖ := pos_iff_ne_zero.mpr hv0
  have hσv : ∀ x : Ωx, νx (σ x) = νx x := fun x => closureValuation_map σ x
  -- `σ` moves `π` and the unit `ϖ / π ^ n` by at most `v(π)` times their valuations
  have hPπ : νx (σ (π : Ωx) - π) ≤ νx (π : Ωx) * νx (π : Ωx) := by
    rw [← pow_two]
    exact hcrit π π.2 hπ1.le
  have huL : ϖ / (π : Ωx) ^ n ∈ L.toIntermediateField := div_mem hϖL (pow_mem π.2 n)
  have hu : νx (ϖ / (π : Ωx) ^ n) = 1 := by
    rw [map_div₀, map_pow, ← hn]
    exact div_self hv0
  have hPu : νx (σ (ϖ / (π : Ωx) ^ n) - ϖ / (π : Ωx) ^ n) ≤
      νx (π : Ωx) * νx (ϖ / (π : Ωx) ^ n) := by
    rw [hu, mul_one]
    calc _ ≤ νx (π : Ωx) ^ 2 := hcrit _ huL hu.le
      _ ≤ νx (π : Ωx) := by
        rw [pow_two]
        exact mul_le_of_le_one_right zero_le hπ1.le
  have hϖeq : ϖ = (π : Ωx) ^ n * (ϖ / (π : Ωx) ^ n) := by
    rw [mul_div_cancel₀ _ (pow_ne_zero n hπ0')]
  have hPϖ : νx (σ ϖ - ϖ) ≤ νx (π : Ωx) * νx ϖ := by
    rw [hϖeq]
    exact map_sub_mul_le νx σ hσv _ (map_sub_pow_le νx σ hσv _ hPπ n) hPu
  -- the root of unity `σ ϖ / ϖ` is congruent to `1`, hence equal to `1`
  have hζN : (σ ϖ / ϖ) ^ N = 1 := by
    rw [div_pow, ← map_pow, hϖ, closureUniformizer_map, div_self (closureUniformizer_ne_zero k)]
  have hζ1 : νx (σ ϖ / ϖ - 1) < 1 := by
    have : σ ϖ / ϖ - 1 = (σ ϖ - ϖ) / ϖ := by
      rw [sub_div, div_self hϖ0]
    rw [this, map_div₀, div_lt_one hϖv0]
    calc νx (σ ϖ - ϖ) ≤ νx (π : Ωx) * νx ϖ := hPϖ
      _ < 1 * νx ϖ := mul_lt_mul_of_pos_right hπ1 hϖv0
      _ = νx ϖ := one_mul _
  have hζint : νx (σ ϖ / ϖ) ≤ 1 := by
    have := congrArg νx hζN
    rw [map_pow, map_one] at this
    exact ((pow_eq_one_iff_of_nonneg zero_le hN0).mp this).le
  have hζeq : (⟨σ ϖ / ϖ, hζint⟩ : 𝔸) = 1 := by
    refine Separable.eq_of_pow_eq_one_of_sub_mem (natCast_isUnit k hN) ?_ (one_pow _) ?_
    · apply Subtype.ext
      simp only [SubmonoidClass.coe_pow, OneMemClass.coe_one]
      exact hζN
    · rw [Separable.mem_maximalIdeal_iff_lt]
      exact hζ1
  have hζ : σ ϖ / ϖ = 1 := congrArg Subtype.val hζeq
  rwa [div_eq_one_iff_eq hϖ0] at hζ

/-- Wild inertia lies in inertia. -/
theorem mem_absoluteInertia_of_forall_lower_one {σ : Gal(Ωx/X)}
    (h : ∀ L : FiniteGaloisIntermediateField X Ωx,
      absoluteFiniteRestriction X Ωx L σ ∈ lowerRamificationGroup (localTopologicalData X L) X 1) :
    σ ∈ absoluteInertia X Ωx := by
  refine mem_absoluteInertia_of_sub_lt_one k fun x hx => ?_
  let L := FiniteGaloisIntermediateField.adjoin X ({x} : Set Ωx)
  have hxL : x ∈ L.toIntermediateField :=
    FiniteGaloisIntermediateField.subset_adjoin X ({x} : Set Ωx) (Set.mem_singleton x)
  obtain ⟨π, hπ0, hπ1, hπ⟩ := exists_levelUniformizer X Ωx L
  exact lt_of_le_of_lt ((mem_lowerRamificationGroup_one_iff k L hπ1 hπ σ).mp (h L) x hxL hx)
    (pow_lt_one₀ zero_le hπ1 two_ne_zero)

/-- An automorphism in inertia fixing the `N`-th roots of `t`, `N` prime to `p`, lies in the
first lower ramification group of every finite Galois level. -/
theorem lower_one_of_fixes_roots {σ : Gal(Ωx/X)} (hσ : σ ∈ absoluteInertia X Ωx)
    (hroot : ∀ N : ℕ, ¬ ringChar k ∣ N → ∀ ϖ : Ωx, ϖ ^ N = closureUniformizer k → σ ϖ = ϖ)
    (L : FiniteGaloisIntermediateField X Ωx) :
    absoluteFiniteRestriction X Ωx L σ ∈ lowerRamificationGroup (localTopologicalData X L) X 1 := by
  obtain ⟨π, hπ0, hπ1, hπ⟩ := exists_levelUniformizer X Ωx L
  rw [mem_lowerRamificationGroup_one_iff k L hπ1 hπ σ]
  have hπ' : ∀ y ∈ L.toIntermediateField, νx y < 1 → νx y ≤ νx (π : Ωx) :=
    fun y hy => hπ ⟨y, hy⟩
  have hπ0' : (π : Ωx) ≠ 0 := by
    intro h0
    rw [h0, map_zero] at hπ0
    exact lt_irrefl _ hπ0
  have hdisc : ∀ y ∈ L.toIntermediateField, νx y < νx (π : Ωx) → νx y ≤ νx (π : Ωx) ^ 2 := by
    intro y hy hlt
    exact le_pow_succ_of_lt_pow hπ0 hπ (y := ⟨y, hy⟩) (n := 1) (by rw [pow_one]; exact hlt)
  have hp : (ringChar k).Prime := Fact.out
  -- `σ` moves the uniformizer `π` into the square of the maximal ideal
  have hA : νx (σ (π : Ωx) - π) ≤ νx (π : Ωx) ^ 2 := by
    apply hdisc _ (sub_mem (apply_mem_level k L σ π.2) π.2)
    obtain ⟨e, he⟩ := exists_closureValuation_eq_pow hπ1 hπ
      (y := ⟨closureUniformizer k, closureUniformizer_mem k L⟩)
      (fun h0 => closureUniformizer_ne_zero k (congrArg Subtype.val h0))
      (closureUniformizer_lt_one k).le
    have he0 : e ≠ 0 := by
      rintro rfl
      rw [pow_zero] at he
      exact (ne_of_lt (closureUniformizer_lt_one k)) he
    obtain ⟨a, m, hm, hem⟩ := Nat.exists_eq_pow_mul_and_not_dvd he0 (ringChar k) hp.one_lt.ne'
    have hmΩ : (m : Ωx) ≠ 0 := by
      intro h
      apply (natCast_isUnit k hm).ne_zero
      apply Subtype.ext
      simpa using h
    have hm0 : m ≠ 0 := fun h => hmΩ (by rw [h, Nat.cast_zero])
    have : NeZero (m : Ωx) := ⟨hmΩ⟩
    obtain ⟨ϖ, hϖ⟩ := IsSepClosed.exists_pow_nat_eq (closureUniformizer k) m
    have hσϖ := hroot m hm ϖ hϖ
    have hϖ0 : ϖ ≠ 0 := by
      rintro rfl
      rw [zero_pow hm0] at hϖ
      exact closureUniformizer_ne_zero k hϖ.symm
    have hϖv : νx ϖ = νx ((π : Ωx) ^ (ringChar k ^ a)) := by
      have h1 : νx ϖ ^ m = νx ((π : Ωx) ^ (ringChar k ^ a)) ^ m := by
        rw [← map_pow, hϖ, ← map_pow, ← pow_mul, ← hem, map_pow]
        exact he
      exact (pow_left_inj₀ zero_le zero_le hm0).mp h1
    have hv0 : νx ϖ ≠ 0 := (Valuation.ne_zero_iff _).mpr hϖ0
    have hy : νx ((π : Ωx) ^ (ringChar k ^ a) / ϖ) = 1 := by
      rw [map_div₀, ← hϖv]
      exact div_self hv0
    have hyσ := sub_lt_one_of_mem_absoluteInertia k hσ hy.le
    have hPy : σ ((π : Ωx) ^ (ringChar k ^ a)) - (π : Ωx) ^ (ringChar k ^ a) =
        ϖ * (σ ((π : Ωx) ^ (ringChar k ^ a) / ϖ) - (π : Ωx) ^ (ringChar k ^ a) / ϖ) := by
      have hP : (π : Ωx) ^ (ringChar k ^ a) = (π : Ωx) ^ (ringChar k ^ a) / ϖ * ϖ := by
        rw [div_mul_cancel₀ _ hϖ0]
      conv_lhs => rw [hP, map_mul, hσϖ]
      ring
    have := closure_charP k
    have hfrob : (σ (π : Ωx) - π) ^ (ringChar k ^ a) =
        σ ((π : Ωx) ^ (ringChar k ^ a)) - (π : Ωx) ^ (ringChar k ^ a) := by
      rw [sub_pow_char_pow, map_pow]
    have hlt : νx (σ (π : Ωx) - π) ^ (ringChar k ^ a) < νx (π : Ωx) ^ (ringChar k ^ a) := by
      rw [← map_pow, hfrob, hPy, map_mul, ← map_pow, ← hϖv]
      calc νx ϖ * νx (σ ((π : Ωx) ^ (ringChar k ^ a) / ϖ) - (π : Ωx) ^ (ringChar k ^ a) / ϖ)
          < νx ϖ * 1 := mul_lt_mul_of_pos_left hyσ (pos_iff_ne_zero.mpr hv0)
        _ = νx ϖ := mul_one _
    exact (pow_lt_pow_iff_left₀ zero_le zero_le (pow_ne_zero _ hp.ne_zero)).mp hlt
  -- every integral element of `L` is a constant plus a multiple of `π`
  intro x hxL hx
  obtain ⟨c, hcL, hxc⟩ := exists_constant_mem_level k L hxL hx
  have hσa : σ ((c : endGenericClosure k) : Ωx) = ((c : endGenericClosure k) : Ωx) := by
    have := (mem_absoluteInertia_iff k σ).mp hσ c
    rw [← completionRestriction_apply]
    exact congrArg Subtype.val this
  have hdL : x - ((c : endGenericClosure k) : Ωx) ∈ L.toIntermediateField := sub_mem hxL hcL
  have hd : νx (x - ((c : endGenericClosure k) : Ωx)) ≤ νx (π : Ωx) := hπ' _ hdL hxc
  obtain ⟨x₁, hx₁⟩ : ∃ x₁ : Ωx, x₁ = (x - ((c : endGenericClosure k) : Ωx)) / (π : Ωx) :=
    ⟨_, rfl⟩
  have hx₁L : x₁ ∈ L.toIntermediateField := by
    rw [hx₁]
    exact div_mem hdL π.2
  have hx₁v : νx x₁ ≤ 1 := by
    rw [hx₁, map_div₀]
    exact div_le_one_of_le₀ hd zero_le
  have hx₁σ : νx (σ x₁ - x₁) ≤ νx (π : Ωx) :=
    hπ' _ (sub_mem (apply_mem_level k L σ hx₁L) hx₁L)
      (sub_lt_one_of_mem_absoluteInertia k hσ hx₁v)
  have hxeq : x = ((c : endGenericClosure k) : Ωx) + (π : Ωx) * x₁ := by
    rw [hx₁, mul_div_cancel₀ _ hπ0']
    ring
  have hsplit : σ x - x = σ (π : Ωx) * (σ x₁ - x₁) + (σ (π : Ωx) - π) * x₁ := by
    rw [hxeq, map_add, map_mul, hσa]
    ring
  rw [hsplit]
  refine (Valuation.map_add _ _ _).trans (max_le ?_ ?_)
  · rw [map_mul, closureValuation_map, pow_two]
    gcongr
  · rw [map_mul]
    calc νx (σ (π : Ωx) - π) * νx x₁ ≤ νx (π : Ωx) ^ 2 * 1 := by gcongr
      _ = νx (π : Ωx) ^ 2 := mul_one _

/-- **Wild inertia of `k((t))`.** An automorphism of the separable closure of `k((t))` lies in
the Library's wild inertia exactly when it lies in the Library's inertia and fixes every root of
`ϖ ^ N = t` with `N` prime to `p`. -/
theorem mem_localWildInertia_iff (σ : Gal(Ωx/X)) :
    σ ∈ localWildInertia X Ωx ↔ σ ∈ absoluteInertia X Ωx ∧
      ∀ N : ℕ, ¬ ringChar k ∣ N → ∀ ϖ : Ωx, ϖ ^ N = closureUniformizer k → σ ϖ = ϖ := by
  have hW : localWildInertia X Ωx = ⨅ L : FiniteGaloisIntermediateField X Ωx,
      (lowerRamificationGroup (localTopologicalData X L) X 1).comap
        (absoluteFiniteRestriction X Ωx L).toMonoidHom :=
    absoluteUpperWildInertia X Ωx
  rw [hW, Subgroup.mem_iInf]
  simp only [Subgroup.mem_comap]
  constructor
  · intro h
    exact ⟨mem_absoluteInertia_of_forall_lower_one k h,
      fun N hN ϖ hϖ => fixes_root_of_forall_lower_one k h hN hϖ⟩
  · rintro ⟨hσ, hroot⟩ L
    exact lower_one_of_fixes_roots k hσ hroot L

/-- **Clause 4.** If restriction is a homeomorphism, it maps the Library's wild inertia onto the
automorphisms fixing the maximal unramified subextension and every root of `ϖ ^ N = t` with `N`
prime to `p`. -/
theorem mem_map_localWildInertia_iff (hr : IsHomeomorph (completionRestriction k))
    (τ : Gal(endGenericClosure k/endField k)) :
    τ ∈ (localWildInertia X Ωx).map (completionRestriction k) ↔
      τ ∈ (endUnramifiedField k).fixingSubgroup ∧
        ∀ (N : ℕ), ¬ ringChar k ∣ N → ∀ ϖ : endGenericClosure k,
          ϖ ^ N = algebraMap (endField k) (endGenericClosure k)
            ((endUniformizer k .zero : endRing k) : endField k) → τ ϖ = ϖ := by
  obtain ⟨σ, rfl⟩ := hr.bijective.surjective τ
  rw [Subgroup.mem_map_iff_mem hr.bijective.injective, mem_localWildInertia_iff,
    mem_fixingSubgroup_endUnramifiedField_iff, ← mem_absoluteInertia_iff]
  refine and_congr Iff.rfl ⟨fun h N hN ϖ hϖ => ?_, fun h N hN ϖ hϖ => ?_⟩
  · apply Subtype.ext
    rw [completionRestriction_apply]
    exact h N hN ϖ (by rw [← IntermediateField.coe_pow, hϖ])
  · have hNΩ : (N : Ωx) ≠ 0 := by
      intro h0
      apply (natCast_isUnit k hN).ne_zero
      apply Subtype.ext
      simpa using h0
    have hmem := mem_endGenericClosure_of_pow_eq_closureUniformizer k hNΩ hϖ
    have := h N hN ⟨ϖ, hmem⟩ (Subtype.ext (by rw [IntermediateField.coe_pow]; exact hϖ))
    have h2 := congrArg Subtype.val this
    rwa [completionRestriction_apply] at h2

end Wild

end Langlands.Henniart.Laumon
