import Langlands.LocalFactor.Ramification.Herbrand.GeneralAbsolute
import Langlands.Galois.Local.ResidueProjectionIntegers

/-!
# Lower ramification groups of finite levels through the valuation of a separable closure

For a nonarchimedean local field `K`, a separable closure `Ω` of `K` and a finite Galois
subextension `L` of `Ω`, the Library's finite-level structure `localTopologicalData K L` has the
valuation induced by `closureValuation K Ω`. Its integer ring is a discrete valuation ring; an
element of `L` of maximal valuation `< 1` is a uniformizer, and the lower ramification groups are
read off `closureValuation K Ω`.
-/

noncomputable section

open ValuativeRel IsLocalRing
open Langlands.LocalGalois Langlands.LocalGalois.SepClosed
open scoped NNReal

namespace Langlands.Ramification.Local

section Generic

variable {L : Type*} [Field L] [ValuativeRel L] {Γ : Type*} [LinearOrderedCommGroupWithZero Γ]
  (w : Valuation L Γ) [w.Compatible]

/-- A valuation compatible with the valuative relation compares elements as the canonical
valuation does. -/
theorem compatible_le_iff (x y : L) : valuation L x ≤ valuation L y ↔ w x ≤ w y :=
  (Valuation.Compatible.vle_iff_le (v := valuation L) x y).symm.trans
    (Valuation.Compatible.vle_iff_le (v := w) x y)

/-- The canonical integers are the elements of compatible valuation at most `1`. -/
theorem compatible_mem_integer_iff (x : L) : x ∈ 𝒪[L] ↔ w x ≤ 1 := by
  rw [Valuation.mem_integer_iff, ← map_one (valuation L), ← map_one w]
  exact compatible_le_iff w x 1

/-- The maximal ideal of the canonical integers is cut out by compatible valuation `< 1`. -/
theorem compatible_mem_maximalIdeal_iff (y : 𝒪[L]) :
    y ∈ maximalIdeal 𝒪[L] ↔ w (y : L) < 1 := by
  rw [mem_maximalIdeal, mem_nonunits_iff, Valuation.Integer.not_isUnit_iff_valuation_lt_one,
    ← map_one (valuation L), ← map_one w, ← not_le, ← not_le]
  exact not_congr (compatible_le_iff w 1 (y : L))

/-- An irreducible integer has compatible valuation `< 1`. -/
theorem compatible_irreducible_lt_one {ϖ : 𝒪[L]} (hϖ : Irreducible ϖ) : w (ϖ : L) < 1 :=
  (compatible_mem_maximalIdeal_iff w ϖ).mp hϖ.not_isUnit

omit [w.Compatible] in
/-- An irreducible integer has positive valuation. -/
theorem compatible_irreducible_pos {ϖ : 𝒪[L]} (hϖ : Irreducible ϖ) : 0 < w (ϖ : L) := by
  rw [pos_iff_ne_zero, ne_eq, map_eq_zero]
  exact fun h => hϖ.ne_zero (Subtype.ext h)

variable [IsDiscreteValuationRing 𝒪[L]]

/-- In a discrete valuation ring of integers, the `n`-th power of the maximal ideal consists of
the elements of valuation at most that of the `n`-th power of a uniformizer. -/
theorem compatible_mem_maximalIdeal_pow_iff {ϖ : 𝒪[L]} (hϖ : Irreducible ϖ) (y : 𝒪[L])
    (n : ℕ) : y ∈ maximalIdeal 𝒪[L] ^ n ↔ w (y : L) ≤ w (ϖ : L) ^ n := by
  rw [hϖ.maximalIdeal_eq, Ideal.span_singleton_pow, Ideal.mem_span_singleton,
    (Valuation.integer.integers (valuation L)).dvd_iff_le, ← map_pow w]
  exact compatible_le_iff w _ _

/-- An element of valuation `< 1` has valuation at most that of a uniformizer. -/
theorem compatible_le_of_lt_one {ϖ : 𝒪[L]} (hϖ : Irreducible ϖ) {y : L} (hy : w y < 1) :
    w y ≤ w (ϖ : L) := by
  have hy1 : y ∈ 𝒪[L] := (compatible_mem_integer_iff w y).mpr hy.le
  have h := (compatible_mem_maximalIdeal_pow_iff w hϖ ⟨y, hy1⟩ 1).mp
    (by rw [pow_one]; exact (compatible_mem_maximalIdeal_iff w ⟨y, hy1⟩).mpr hy)
  simpa only [pow_one] using h

/-- Every nonzero integral element has the valuation of a power of a uniformizer. -/
theorem compatible_exists_eq_pow {ϖ : 𝒪[L]} (hϖ : Irreducible ϖ) {y : L} (hy0 : y ≠ 0)
    (hy : w y ≤ 1) : ∃ n : ℕ, w y = w (ϖ : L) ^ n := by
  have hy1 : y ∈ 𝒪[L] := (compatible_mem_integer_iff w y).mpr hy
  obtain ⟨n, u, hu⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible
    (x := (⟨y, hy1⟩ : 𝒪[L])) (fun h => hy0 (congrArg Subtype.val h)) hϖ
  refine ⟨n, ?_⟩
  have hval : w ((u : 𝒪[L]) : L) = 1 := by
    have h1 := (Valuation.integer.integers (valuation L)).valuation_unit u
    have h2 := compatible_le_iff w ((u : 𝒪[L]) : L) 1
    have h3 := compatible_le_iff w 1 ((u : 𝒪[L]) : L)
    simp only [map_one] at h2 h3
    change valuation L ((u : 𝒪[L]) : L) = 1 at h1
    exact le_antisymm (h2.mp h1.le) (h3.mp h1.ge)
  have : y = ((u : 𝒪[L]) : L) * (ϖ : L) ^ n := congrArg Subtype.val hu
  rw [this, map_mul, hval, one_mul, map_pow]

end Generic

section Moves

variable {R : Type*} [CommRing R] (v : Valuation R ℝ≥0) {F : Type*} [FunLike F R R]
  [RingHomClass F R R] (f : F) (hf : ∀ x, v (f x) = v x) (c : ℝ≥0)
include hf

/-- If a valuation-preserving ring endomorphism `f` moves `a` and `b` by at most `c` times their
valuations, it moves `a * b` by at most `c` times its valuation. -/
theorem map_sub_mul_le {a b : R} (ha : v (f a - a) ≤ c * v a) (hb : v (f b - b) ≤ c * v b) :
    v (f (a * b) - a * b) ≤ c * v (a * b) := by
  have hsplit : f (a * b) - a * b = f a * (f b - b) + (f a - a) * b := by
    rw [map_mul]
    ring
  rw [hsplit, map_mul v a b]
  refine (Valuation.map_add _ _ _).trans (max_le ?_ ?_)
  · rw [map_mul, hf]
    calc v a * v (f b - b) ≤ v a * (c * v b) := by gcongr
      _ = c * (v a * v b) := by ring
  · rw [map_mul]
    calc v (f a - a) * v b ≤ c * v a * v b := by gcongr
      _ = c * (v a * v b) := by ring

/-- The same bound for the powers of `a`. -/
theorem map_sub_pow_le {a : R} (ha : v (f a - a) ≤ c * v a) (n : ℕ) :
    v (f (a ^ n) - a ^ n) ≤ c * v (a ^ n) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ]
    exact map_sub_mul_le v f hf c ih ha

end Moves

section IntegerIndex

universe u₀ uK uL

variable {K₀ : Type u₀} [Field K₀] [ValuativeRel K₀] [TopologicalSpace K₀]
  {L : Type uL} [Field L] [Algebra K₀ L]
  (T : LocalField.TopologicalData K₀ L) (K : Type uK) [Field K] [Algebra K₀ K]
  [Algebra K L] [IsScalarTower K₀ K L]

/-- The integer-indexed lower groups: the whole group below `0`, the `i`-th lower group at
`i ≥ 0`. -/
theorem mem_lowerRamificationGroupInt_iff (i : ℤ) (g : L ≃ₐ[K] L) :
    g ∈ lowerRamificationGroupInt T K i ↔ i < 0 ∨ g ∈ lowerRamificationGroup T K i.toNat := by
  unfold lowerRamificationGroupInt lowerGroupInt
  by_cases hi : i < 0
  · simp only [hi, ite_true, Subgroup.mem_top, true_or]
  · simp only [hi, ite_false, false_or]
    rfl

end IntegerIndex

section Closure

universe uK uΩ

variable (K : Type uK) [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K] (Ω : Type uΩ) [Field Ω] [Algebra K Ω] [IsSepClosure K Ω]

local instance : Algebra.IsAlgebraic K Ω := Algebra.IsSeparable.isAlgebraic K Ω
local instance : NontriviallyNormedField K := localNormedField K
local instance : IsUltrametricDist K := localNormedField_ultrametric K
local instance : CompleteSpace K := localNormedField_complete K

variable (L : FiniteGaloisIntermediateField K Ω)

/-- The valuation of a finite level `L`, the restriction of `closureValuation K Ω`. -/
def levelValuation : Valuation L ℝ≥0 :=
  (closureValuation K Ω).comap (algebraMap L Ω)

@[simp] theorem levelValuation_apply (x : L) :
    levelValuation K Ω L x = closureValuation K Ω (x : Ω) := rfl

/-- The restricted valuation is the spectral valuation of the finite level. -/
theorem levelValuation_eq_spectralValuation :
    levelValuation K Ω L = spectralValuation K L := by
  ext x
  change spectralNorm K Ω (algebraMap L Ω x) = spectralNorm K L x
  exact (spectralNorm.eq_of_tower x).symm

/-- The valuation of the Library's finite-level structure `localTopologicalData K L` is induced by
`closureValuation K Ω`. -/
theorem levelValuation_compatible :
    letI := (localTopologicalData K L).valuativeRel
    (levelValuation K Ω L).Compatible := by
  rw [levelValuation_eq_spectralValuation]
  exact Valuation.Compatible.ofValuation _

/-- The integers of the finite level are its elements of valuation at most `1`. -/
theorem mem_localIntegers_iff (x : L) :
    x ∈ (localTopologicalData K L).Integers ↔ closureValuation K Ω (x : Ω) ≤ 1 := by
  let := (localTopologicalData K L).valuativeRel
  have := levelValuation_compatible K Ω L
  exact compatible_mem_integer_iff (levelValuation K Ω L) x

/-- A uniformizer of the finite level, in terms of `closureValuation K Ω`. -/
theorem exists_levelUniformizer :
    ∃ π : L, 0 < closureValuation K Ω (π : Ω) ∧ closureValuation K Ω (π : Ω) < 1 ∧
      ∀ y : L, closureValuation K Ω (y : Ω) < 1 →
        closureValuation K Ω (y : Ω) ≤ closureValuation K Ω (π : Ω) := by
  let := (localTopologicalData K L).topology
  let := (localTopologicalData K L).valuativeRel
  let := (localTopologicalData K L).localField
  have := levelValuation_compatible K Ω L
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible 𝒪[L]
  exact ⟨ϖ, compatible_irreducible_pos (levelValuation K Ω L) hϖ,
    compatible_irreducible_lt_one (levelValuation K Ω L) hϖ,
    fun y hy => compatible_le_of_lt_one (levelValuation K Ω L) hϖ hy⟩

variable {K Ω L}

/-- An element of maximal valuation `< 1` has the valuation of an irreducible element of the
integer ring. -/
theorem exists_irreducible_eq_of_isMax {π : L} (hπ1 : closureValuation K Ω (π : Ω) < 1)
    (hπ : ∀ y : L, closureValuation K Ω (y : Ω) < 1 →
      closureValuation K Ω (y : Ω) ≤ closureValuation K Ω (π : Ω)) :
    letI := (localTopologicalData K L).valuativeRel
    ∃ ϖ : 𝒪[L], Irreducible ϖ ∧ closureValuation K Ω ((ϖ : L) : Ω) =
      closureValuation K Ω (π : Ω) := by
  let := (localTopologicalData K L).topology
  let := (localTopologicalData K L).valuativeRel
  let := (localTopologicalData K L).localField
  have := levelValuation_compatible K Ω L
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible 𝒪[L]
  refine ⟨ϖ, hϖ, le_antisymm ?_ ?_⟩
  · exact hπ ϖ (compatible_irreducible_lt_one (levelValuation K Ω L) hϖ)
  · exact compatible_le_of_lt_one (levelValuation K Ω L) hϖ hπ1

/-- Every nonzero integral element of a finite level has the valuation of a power of a
uniformizer. -/
theorem exists_closureValuation_eq_pow {π : L} (hπ1 : closureValuation K Ω (π : Ω) < 1)
    (hπ : ∀ y : L, closureValuation K Ω (y : Ω) < 1 →
      closureValuation K Ω (y : Ω) ≤ closureValuation K Ω (π : Ω))
    {y : L} (hy0 : y ≠ 0) (hy : closureValuation K Ω (y : Ω) ≤ 1) :
    ∃ n : ℕ, closureValuation K Ω (y : Ω) = closureValuation K Ω (π : Ω) ^ n := by
  let := (localTopologicalData K L).topology
  let := (localTopologicalData K L).valuativeRel
  let := (localTopologicalData K L).localField
  have := levelValuation_compatible K Ω L
  obtain ⟨ϖ, hϖ, hv⟩ := exists_irreducible_eq_of_isMax hπ1 hπ
  rw [← hv]
  exact compatible_exists_eq_pow (levelValuation K Ω L) hϖ hy0 hy


/-- An element of a finite level of valuation `< v(π) ^ n`, for `π` of maximal valuation `< 1`,
has valuation at most `v(π) ^ (n + 1)`. -/
theorem le_pow_succ_of_lt_pow {π : L} (hπ0 : 0 < closureValuation K Ω (π : Ω))
    (hπ : ∀ y : L, closureValuation K Ω (y : Ω) < 1 →
      closureValuation K Ω (y : Ω) ≤ closureValuation K Ω (π : Ω))
    {y : L} {n : ℕ} (hy : closureValuation K Ω (y : Ω) < closureValuation K Ω (π : Ω) ^ n) :
    closureValuation K Ω (y : Ω) ≤ closureValuation K Ω (π : Ω) ^ (n + 1) := by
  have hc : 0 < closureValuation K Ω (π : Ω) ^ n := pow_pos hπ0 n
  have hz : closureValuation K Ω ((y / π ^ n : L) : Ω) =
      closureValuation K Ω (y : Ω) / closureValuation K Ω (π : Ω) ^ n := by
    rw [IntermediateField.coe_div, IntermediateField.coe_pow, map_div₀, map_pow]
  have hz1 : closureValuation K Ω ((y / π ^ n : L) : Ω) < 1 := by
    rw [hz]
    exact (div_lt_one hc).mpr hy
  have := hπ _ hz1
  rw [hz, div_le_iff₀ hc] at this
  rwa [pow_succ, mul_comm]

/-- **Lower ramification groups through `closureValuation`.** For an element `π` of `L` of
maximal valuation `< 1`, an automorphism `g` of `L` lies in the Library's `i`-th lower
ramification group of `localTopologicalData K L` exactly when it moves every integral element
of `L` by an element of valuation at most `v(π) ^ (i + 1)`. -/
theorem mem_lowerRamificationGroup_iff_closureValuation {π : L}
    (hπ1 : closureValuation K Ω (π : Ω) < 1)
    (hπ : ∀ y : L, closureValuation K Ω (y : Ω) < 1 →
      closureValuation K Ω (y : Ω) ≤ closureValuation K Ω (π : Ω))
    (g : Gal(L/K)) (i : ℕ) :
    g ∈ lowerRamificationGroup (localTopologicalData K L) K i ↔
      ∀ x : L, closureValuation K Ω (x : Ω) ≤ 1 →
        closureValuation K Ω ((g x - x : L) : Ω) ≤ closureValuation K Ω (π : Ω) ^ (i + 1) := by
  let := (localTopologicalData K L).topology
  let := (localTopologicalData K L).valuativeRel
  let := (localTopologicalData K L).localField
  have := levelValuation_compatible K Ω L
  obtain ⟨ϖ, hϖ, hv⟩ := exists_irreducible_eq_of_isMax hπ1 hπ
  rw [mem_lowerRamificationGroup]
  constructor
  · intro h x hx
    have hx' : x ∈ 𝒪[L] := (mem_localIntegers_iff K Ω L x).mpr hx
    have := (compatible_mem_maximalIdeal_pow_iff (levelValuation K Ω L) hϖ _ (i + 1)).mp
      (h ⟨x, hx'⟩)
    rw [levelValuation_apply, levelValuation_apply, hv] at this
    exact this
  · intro h x
    have hx : closureValuation K Ω ((x : L) : Ω) ≤ 1 :=
      (mem_localIntegers_iff K Ω L x).mp x.property
    rw [compatible_mem_maximalIdeal_pow_iff (levelValuation K Ω L) hϖ, levelValuation_apply,
      levelValuation_apply, hv]
    exact h x hx

end Closure

end Langlands.Ramification.Local
