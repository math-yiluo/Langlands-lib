import Langlands.GaloisCohomology.Local.Arithmetic.Units
import Langlands.GaloisCohomology.Local.Arithmetic.Extension
import Langlands.GaloisCohomology.Local.Arithmetic.Uniqueness
import Langlands.Galois.Local.AbsoluteDefinitions
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.RingTheory.DedekindDomain.Ideal.Lemmas
import Mathlib.RingTheory.Localization.Module

/-!
# Rings of integers of finite extensions of local fields

For a finite extension `L/K` of nonarchimedean local fields: `𝒪[L]` is a finite free
`𝒪[K]`-module of rank `[L : K]` and the integral closure of `𝒪[K]` in `L`; the cardinality of
`𝒪[K]/(ϖⁿ)`; roots of unity of order prime to the residue characteristic are determined by their
residues; the action of `L ≃ₐ[K] L` on `𝒪[L]ˣ`.
-/

noncomputable section

namespace Langlands.GaloisCohomology.Local

open ValuativeRel IsLocalRing Polynomial

section Basic

variable {K : Type*} [Field K] [ValuativeRel K]

theorem mem_maximalIdeal_integer_iff {x : 𝒪[K]} : x ∈ 𝓂[K] ↔ valuation K (x : K) < 1 := by
  rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
  exact Valuation.Integer.not_isUnit_iff_valuation_lt_one

theorem mem_integer_of_pow_eq_one {m : ℕ} (hm : m ≠ 0) {x : K} (hx : x ^ m = 1) : x ∈ 𝒪[K] := by
  rw [Valuation.mem_integer_iff]
  have h : valuation K x ^ m = 1 := by rw [← map_pow, hx, map_one]
  refine le_of_not_gt fun h1 ↦ ?_
  have := one_lt_pow₀ h1 hm
  rw [h] at this
  exact this.false

variable [TopologicalSpace K] [IsNonarchimedeanLocalField K]

/-- Roots of unity of order invertible in the residue field are determined by their residues. -/
theorem eq_of_pow_eq_one_of_residue_eq {m : ℕ} (hm : (m : 𝓀[K]) ≠ 0) {x y : 𝒪[K]}
    (hx : x ^ m = 1) (hy : y ^ m = 1) (h : residue 𝒪[K] x = residue 𝒪[K] y) : x = y := by
  have hm0 : m ≠ 0 := by rintro rfl; simp at hm
  have hxu : IsUnit x := (isUnit_pow_iff hm0).mp (hx ▸ isUnit_one)
  refine IsLocalRing.eq_of_eval_eq_zero_of_not_isUnit_sub (f := X ^ m - C 1)
    (by simp [hx]) (by simp [hy]) ?_ ?_
  · rw [← mem_nonunits_iff, ← IsLocalRing.mem_maximalIdeal, ← residue_eq_zero_iff,
      map_sub, h, sub_self]
  · simp only [derivative_sub, derivative_X_pow, derivative_C, sub_zero, eval_mul,
      eval_pow, eval_X]
    refine IsUnit.mul ?_ (hxu.pow _)
    rw [← residue_ne_zero_iff_isUnit]
    simpa using hm

theorem exists_pow_lt {ϖ : 𝒪[K]} (hϖ : Irreducible ϖ) {γ : ValueGroupWithZero K} (hγ : γ ≠ 0) :
    ∃ n, 1 ≤ n ∧ valuation K (ϖ : K) ^ n < γ := by
  have h1 : valuation K (ϖ : K) < 1 :=
    valuation_lt_one_of_mem_maximalIdeal (uniformizer_mem_maximalIdeal hϖ)
  obtain ⟨n, hn⟩ := exists_pow_lt₀ h1 (Units.mk0 γ hγ)
  refine ⟨n + 1, Nat.le_add_left 1 n, ?_⟩
  calc valuation K (ϖ : K) ^ (n + 1) ≤ valuation K (ϖ : K) ^ n :=
        pow_le_pow_right_of_le_one' h1.le (Nat.le_succ n)
    _ < γ := hn

variable {π : 𝒪[K]}

theorem card_quotient_span_pow (hπ : Irreducible π) (n : ℕ) :
    Nat.card (𝒪[K] ⧸ Ideal.span {π ^ n}) = Nat.card 𝓀[K] ^ n := by
  have h : Ideal.span {π ^ n} = IsLocalRing.maximalIdeal 𝒪[K] ^ n := by
    rw [hπ.maximalIdeal_eq, Ideal.span_singleton_pow]
  rw [h, ← Submodule.cardQuot_apply, cardQuot_pow_of_prime
    (IsDiscreteValuationRing.not_a_field 𝒪[K]), Submodule.cardQuot_apply]
  rfl

end Basic

section Finite

variable (K L : Type*) [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  [Field L] [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L]
  [Algebra K L] [ValuativeExtension K L] [FiniteDimensional K L]

theorem exists_basis_coord_bound : ∃ a : K, a ≠ 0 ∧ ∀ x : L, valuation L x ≤ 1 →
    ∀ i, valuation K ((Module.finBasis K L).repr x i / a) ≤ 1 := by
  let := LocalGalois.localNormedField K
  have := LocalGalois.localNormedField_complete K
  have := t2Space_of_isNonarchimedeanLocalField L
  let b := Module.finBasis K L
  let e := b.equivFun.toContinuousLinearEquiv
  have hc : IsCompact (e '' {x : L | valuation L x ≤ 1}) :=
    (IsNonarchimedeanLocalField.isCompact_closedBall L 1).image e.continuous
  obtain ⟨r, hr⟩ := (Metric.isBounded_iff_subset_closedBall 0).1 hc.isBounded
  obtain ⟨a, ha⟩ := NormedField.exists_lt_norm K (max r 1)
  have ha0 : 0 < ‖a‖ := lt_of_lt_of_le zero_lt_one (le_max_right r 1) |>.trans ha
  refine ⟨a, norm_pos_iff.1 ha0, fun x hx i => ?_⟩
  have h1 : ‖e x‖ ≤ r := by simpa using hr ⟨x, hx, rfl⟩
  have h2 : ‖b.repr x i‖ ≤ r := (norm_le_pi_norm (e x) i).trans h1
  have h3 : ‖b.repr x i / a‖ ≤ ‖(1 : K)‖ := by
    rw [norm_div, norm_one, div_le_one ha0]
    exact h2.trans ((le_max_left r 1).trans ha.le)
  have := (LocalGalois.localNormedField_le K _ _).1 h3
  rwa [map_one] at this

/-- `𝒪[L]` is a finite `𝒪[K]`-module. -/
instance moduleFinite_integer : Module.Finite 𝒪[K] 𝒪[L] := by
  obtain ⟨a, ha, hb⟩ := exists_basis_coord_bound K L
  let b := Module.finBasis K L
  let N : Submodule 𝒪[K] L := Submodule.span 𝒪[K] (Set.range fun i => a • b i)
  have hN : N.FG := Submodule.fg_span (Set.finite_range _)
  have : IsNoetherian 𝒪[K] N := isNoetherian_of_fg_of_noetherian N hN
  have hmem : ∀ x : 𝒪[L], (x : L) ∈ N := by
    intro x
    have hx : valuation L (x : L) ≤ 1 := x.2
    rw [← b.sum_repr (x : L)]
    refine Submodule.sum_mem _ fun i _ => ?_
    have hc := hb x hx i
    have : b.repr x i • b i = (⟨b.repr x i / a, hc⟩ : 𝒪[K]) • (a • b i) := by
      rw [← algebraMap_smul K (⟨_, hc⟩ : 𝒪[K]) (a • b i), smul_smul]
      congr 1
      exact (div_mul_cancel₀ _ ha).symm
    rw [this]
    exact N.smul_mem _ (Submodule.subset_span ⟨i, rfl⟩)
  let f : 𝒪[L] →ₗ[𝒪[K]] N :=
    LinearMap.codRestrict N ((IsScalarTower.toAlgHom 𝒪[K] 𝒪[L] L).toLinearMap) fun x => hmem x
  refine Module.Finite.of_injective f fun x y h => ?_
  have h' := congrArg Subtype.val h
  exact Subtype.ext h'

/-- `𝒪[L]` is a free `𝒪[K]`-module. -/
instance moduleFree_integer : Module.Free 𝒪[K] 𝒪[L] := Module.free_of_finite_type_torsion_free'

omit [TopologicalSpace K] [IsNonarchimedeanLocalField K] [TopologicalSpace L]
  [IsNonarchimedeanLocalField L] [FiniteDimensional K L] in
theorem finrank_integer : Module.finrank 𝒪[K] 𝒪[L] = Module.finrank K L :=
  (IsFractionRing.finrank_eq 𝒪[K] K 𝒪[L] L).symm

end Finite

section Galois

variable {K L : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K]
  [Field L] [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L]
  [Algebra K L] [ValuativeExtension K L] [FiniteDimensional K L]

variable (K L) in
/-- The action of `L ≃ₐ[K] L` on `𝒪[L]ˣ`. -/
@[instance_reducible]
def integerUnitsAction : MulDistribMulAction (L ≃ₐ[K] L) 𝒪[L]ˣ where
  smul σ u := Units.map (integerAlgEquiv K L σ : 𝒪[L] →* 𝒪[L]) u
  one_smul u := by ext; rfl
  mul_smul σ τ u := by ext; rfl
  smul_mul σ u w := map_mul (Units.map (integerAlgEquiv K L σ : 𝒪[L] →* 𝒪[L])) u w
  smul_one σ := map_one (Units.map (integerAlgEquiv K L σ : 𝒪[L] →* 𝒪[L]))

attribute [local instance] integerUnitsAction

@[simp]
theorem coe_smul_integerUnits (σ : L ≃ₐ[K] L) (u : 𝒪[L]ˣ) :
    (((σ • u : 𝒪[L]ˣ) : 𝒪[L]) : L) = σ ((u : 𝒪[L]) : L) :=
  rfl

theorem integerUnitsMap_smul (σ : L ≃ₐ[K] L) (u : 𝒪[L]ˣ) :
    integerUnitsMap L (σ • u) = σ • integerUnitsMap L u := by
  ext
  rfl

end Galois

end Langlands.GaloisCohomology.Local
