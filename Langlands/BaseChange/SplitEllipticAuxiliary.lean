import Langlands.BaseChange.RegularEllipticOpen
import Langlands.BaseChange.SplitMatchingChart
import Mathlib.RingTheory.Polynomial.Eisenstein.Basic

/-! # Regular elliptic norm pairs at a split auxiliary place -/

noncomputable section

namespace Langlands.BaseChange

open JacquetLanglands _root_.Polynomial

universe u

section Existence

variable (F : Type u) [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F] [CharZero F]

local notation "𝒪F" => Valuation.integer (ValuativeRel.valuation F)

/-- An elliptic source for the split norm can be chosen with nonzero trace. -/
theorem exists_regularElliptic_trace_ne_zero (r : ℕ) :
    ∃ γ : GeneralLinear (r + 1) F, IsRegularElliptic γ ∧ Matrix.trace γ.val ≠ 0 := by
  cases r with
  | zero =>
    let p : F[X] := X - C 1
    have h0 : p.coeff 0 ≠ 0 := by simp [p]
    obtain ⟨γ, hγ⟩ := exists_generalLinear_charpoly_eq p (monic_X_sub_C 1)
      (natDegree_X_sub_C 1) h0
    have hi : Irreducible p := irreducible_X_sub_C 1
    refine ⟨γ, ⟨?_, ?_⟩, ?_⟩
    · change γ.val.charpoly.Separable
      rw [hγ]
      exact PerfectField.separable_of_irreducible hi
    · rwa [hγ]
    · simpa only [Matrix.trace_eq_neg_charpoly_coeff, Fintype.card_fin, Nat.sub_self, hγ, neg_ne_zero]
        using h0
  | succ r =>
    obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible 𝒪F
    let p : 𝒪F[X] := X ^ (r + 2) + (C π * X ^ (r + 1) + C π)
    have hlower : (C π * X ^ (r + 1) + C π).degree < ((r + 2 : ℕ) : WithBot ℕ) := by
      have h := degree_add_le_of_degree_le (degree_C_mul_X_pow_le (r + 1) π)
        (degree_C_le.trans (by exact_mod_cast Nat.zero_le (r + 1)) : (C π).degree ≤ (r + 1 : ℕ))
      exact h.trans_lt (by exact_mod_cast Nat.lt_succ_self (r + 1))
    have hm : p.Monic := monic_X_pow_add hlower
    have hd : p.natDegree = r + 2 := by
      unfold p
      exact natDegree_add_eq_left_of_degree_lt (by simpa only [degree_X_pow] using hlower)
        |>.trans (natDegree_X_pow _)
    let I := IsLocalRing.maximalIdeal 𝒪F
    have hπI : π ∈ I := (IsLocalRing.mem_maximalIdeal _).mpr hπ.not_isUnit
    have h0 : p.coeff 0 = π := by
      simp [p, coeff_X_pow]
    have htop : p.coeff (r + 1) = π := by
      simp [p, coeff_X_pow]
    have hπI2 : π ∉ I ^ 2 := by
      change π ∉ (IsLocalRing.maximalIdeal 𝒪F) ^ 2
      rw [hπ.maximalIdeal_eq, Ideal.span_singleton_pow, Ideal.mem_span_singleton]
      rintro ⟨a, ha⟩
      have h1 : 1 = π * a :=
        mul_left_cancel₀ hπ.ne_zero (by simpa only [mul_one, ← mul_assoc, ← pow_two] using ha)
      exact hπ.not_isUnit (isUnit_of_dvd_one ⟨a, h1⟩)
    have he : p.IsEisensteinAt I := by
      apply hm.isEisensteinAt_of_mem_of_notMem (Ideal.IsPrime.ne_top inferInstance)
      · intro i hi
        have hin : i ≠ r + 2 := (hd ▸ hi).ne
        by_cases hi0 : i = 0
        · simpa [hi0, h0] using hπI
        by_cases hi1 : i = r + 1
        · simpa [hi1, htop] using hπI
        have hcoeff : p.coeff i = 0 := by
          simp [p, coeff_X_pow, coeff_C, hin, hi0, hi1]
        rw [hcoeff]
        exact Ideal.zero_mem I
      · rwa [h0]
    let q := p.map (algebraMap 𝒪F F)
    have hi : Irreducible q := (hm.irreducible_iff_irreducible_map_fraction_map (K := F)).mp
      (he.irreducible inferInstance hm.isPrimitive (hd ▸ Nat.zero_lt_succ (r + 1)))
    have hπF : algebraMap 𝒪F F π ≠ 0 := (FaithfulSMul.algebraMap_injective 𝒪F F).ne hπ.ne_zero
    have hq0 : q.coeff 0 ≠ 0 := by
      rwa [coeff_map, h0]
    have hqdeg : q.natDegree = r + 2 := by
      unfold q
      rw [hm.natDegree_map, hd]
    obtain ⟨γ, hγ⟩ := exists_generalLinear_charpoly_eq q (hm.map _) hqdeg hq0
    refine ⟨γ, ⟨?_, ?_⟩, ?_⟩
    · change γ.val.charpoly.Separable
      rw [hγ]
      exact PerfectField.separable_of_irreducible hi
    · rwa [hγ]
    · rw [Matrix.trace_eq_neg_charpoly_coeff, Fintype.card_fin, hγ, neg_ne_zero]
      change q.coeff (r + 1) ≠ 0
      rwa [coeff_map, htop]

/-- The locus used to choose the split auxiliary test is open. -/
theorem isOpen_regularElliptic_trace_ne_zero (n : ℕ) :
    IsOpen {γ : GeneralLinear n F | IsRegularElliptic γ ∧ Matrix.trace γ.val ≠ 0} := by
  let : T2Space F := LocalFieldTopology.t2Space F
  have hval : Continuous (fun γ : GeneralLinear n F => γ.val) := Units.continuous_val
  have htrace : Continuous (fun γ : GeneralLinear n F => Matrix.trace γ.val) := by
    unfold Matrix.trace
    apply continuous_finsetSum
    intro i _
    have hentry : Continuous (fun A : Matrix (Fin n) (Fin n) F => A i i) :=
      (continuous_apply i).comp (continuous_apply i)
    exact hentry.comp hval
  exact (isOpen_regularElliptic F n).inter (isOpen_ne.preimage htrace)

end Existence

/-- Nonzero trace rules out any nontrivial scalar in a conjugacy relation. -/
theorem scalar_eq_one_of_conj_eq_scalar_mul {F : Type u} [Field F] {n : ℕ}
    {γ : GeneralLinear n F} (hγ : Matrix.trace γ.val ≠ 0)
    {a : Fˣ} {x : GeneralLinear n F} (h : x⁻¹ * γ * x = GeneralLinear.scalar a * γ) : a = 1 := by
  have ht := congrArg (fun y : GeneralLinear n F => Matrix.trace y.val) h
  change Matrix.trace ((x⁻¹ : GeneralLinear n F).val * γ.val * x.val) =
    Matrix.trace (Matrix.scalar (Fin n) (a : F) * γ.val) at ht
  rw [Matrix.trace_units_conj', Matrix.scalar_apply, ← Matrix.smul_eq_diagonal_mul,
    Matrix.trace_smul, smul_eq_mul] at ht
  apply Units.ext
  exact mul_right_cancel₀ hγ (ht.symm.trans (one_mul _).symm)

/-- A split cyclic algebra has an associated pair whose ordinary element
is regular elliptic and has no scalar conjugacy ambiguity. -/
def SplitEllipticAuxiliaryStatement : Prop :=
  ∀ (F : Type u) [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F] [CharZero F] (r m : ℕ),
    ∃ (δ : GeneralLinear (r + 1) (Fin (m + 1) → F)) (γ : GeneralLinear (r + 1) F),
      IsNormAssociated (splitCyclicShift F (m + 1)) (m + 1) δ γ ∧
        IsRegularElliptic γ ∧ Matrix.trace γ.val ≠ 0

theorem splitEllipticAuxiliary : SplitEllipticAuxiliaryStatement.{u} := by
  intro F _ _ _ _ _ r m
  obtain ⟨γ, hγ, htrace⟩ := exists_regularElliptic_trace_ne_zero F r
  obtain ⟨δ, hassoc⟩ := isNorm_splitCyclicShift (l := m) γ
  exact ⟨δ, γ, hassoc, hγ, htrace⟩

end Langlands.BaseChange
