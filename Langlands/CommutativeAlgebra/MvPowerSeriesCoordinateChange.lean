import Mathlib.RingTheory.MvPowerSeries.Substitution
import Mathlib.Order.PiLex
import Mathlib.Data.DFinsupp.WellFounded

/-! # A coordinate change making a power series regular in the first variable -/

namespace Langlands.CommutativeAlgebra.MvPowerSeriesFactorial

open MvPowerSeries

section Weight

/-- A sum `∑ α i * s ^ i` with all digits `α i < s` is smaller than `s ^ m`. -/
theorem sum_mul_pow_lt (s : ℕ) :
    ∀ {m : ℕ} (α : Fin m → ℕ), (∀ i, α i < s) → ∑ i, α i * s ^ (i : ℕ) < s ^ m := by
  intro m
  induction m with
  | zero => intro α _; simp
  | succ m ih =>
    intro α hα
    rw [Fin.sum_univ_castSucc]
    have h1 := ih (fun i => α (Fin.castSucc i)) (fun i => hα _)
    have h2 : α (Fin.last m) + 1 ≤ s := hα _
    simp only [Fin.val_castSucc, Fin.val_last] at h1 ⊢
    calc ∑ i : Fin m, α (Fin.castSucc i) * s ^ (i : ℕ) + α (Fin.last m) * s ^ m
        < s ^ m + α (Fin.last m) * s ^ m := by omega
      _ = (α (Fin.last m) + 1) * s ^ m := by ring
      _ ≤ s * s ^ m := Nat.mul_le_mul_right _ h2
      _ = s ^ (m + 1) := by ring

/-- If all digits of `α` are smaller than `s` and `α` is colexicographically smaller than `d`,
then the weight `∑ α i * s ^ i` is smaller than `∑ d i * s ^ i`. -/
theorem sum_mul_pow_lt_of_colex (s : ℕ) :
    ∀ {m : ℕ} (α d : Fin m → ℕ), (∀ i, α i < s) →
      (∃ i, (∀ j, i < j → α j = d j) ∧ α i < d i) →
      ∑ i, α i * s ^ (i : ℕ) < ∑ i, d i * s ^ (i : ℕ) := by
  intro m
  induction m with
  | zero => intro α d _ h; obtain ⟨i, _⟩ := h; exact i.elim0
  | succ m ih =>
    intro α d hα ⟨i, hi, hlt⟩
    rw [Fin.sum_univ_castSucc, Fin.sum_univ_castSucc]
    simp only [Fin.val_castSucc, Fin.val_last]
    rcases Fin.eq_castSucc_or_eq_last i with ⟨i', rfl⟩ | rfl
    · have hl : α (Fin.last m) = d (Fin.last m) := hi _ (Fin.castSucc_lt_last i')
      have := ih (fun j => α (Fin.castSucc j)) (fun j => d (Fin.castSucc j)) (fun j => hα _)
        ⟨i', fun j hj => hi _ (Fin.castSucc_lt_castSucc_iff.mpr hj), hlt⟩
      rw [hl]
      omega
    · have h1 := sum_mul_pow_lt s (fun j => α (Fin.castSucc j)) (fun j => hα _)
      have h2 : (α (Fin.last m) + 1) * s ^ m ≤ d (Fin.last m) * s ^ m :=
        Nat.mul_le_mul_right _ hlt
      have h3 : (α (Fin.last m) + 1) * s ^ m = α (Fin.last m) * s ^ m + s ^ m := by ring
      omega

end Weight

section CoordinateChange

variable {K : Type*} [CommRing K] {n : ℕ}

/-- The substitution family `X 0 ↦ X 0` and `X i ↦ X i + c • X 0 ^ (s ^ i)` for `i ≠ 0`. -/
noncomputable def coordFamily (s : ℕ) (c : K) : Fin (n + 1) → MvPowerSeries (Fin (n + 1)) K :=
  fun i => if i = 0 then X 0 else X i + c • X 0 ^ (s ^ (i : ℕ))

theorem hasSubst_coordFamily {s : ℕ} (hs : s ≠ 0) (c : K) :
    HasSubst (coordFamily (n := n) s c) :=
  hasSubst_of_constantCoeff_zero fun i => by
    unfold coordFamily
    split_ifs with hi
    · simp
    · simp [zero_pow (pow_ne_zero _ hs)]

theorem coordFamily_apply_zero (s : ℕ) (c : K) : coordFamily (n := n) s c 0 = X 0 := by
  simp [coordFamily]

theorem coordFamily_apply_of_ne (s : ℕ) (c : K) {i : Fin (n + 1)} (hi : i ≠ 0) :
    coordFamily s c i = X i + c • X 0 ^ (s ^ (i : ℕ)) := by
  simp [coordFamily, hi]

theorem subst_coordFamily_coordFamily {s : ℕ} (hs : s ≠ 0) (c d : K) (i : Fin (n + 1)) :
    subst (coordFamily s d) (coordFamily s c i) = coordFamily (n := n) s (c + d) i := by
  have hd := hasSubst_coordFamily (n := n) hs d
  by_cases hi : i = 0
  · rw [hi, coordFamily_apply_zero, coordFamily_apply_zero, subst_X hd, coordFamily_apply_zero]
  · rw [coordFamily_apply_of_ne _ _ hi, coordFamily_apply_of_ne _ _ hi, subst_add hd,
      subst_smul hd, subst_pow hd, subst_X hd, subst_X hd, coordFamily_apply_of_ne _ _ hi,
      coordFamily_apply_zero, add_smul]
    abel

theorem subst_coordFamily_subst {s : ℕ} (hs : s ≠ 0) (c d : K) (f : MvPowerSeries (Fin (n + 1)) K) :
    subst (coordFamily s d) (subst (coordFamily s c) f) = subst (coordFamily s (c + d)) f := by
  rw [subst_comp_subst_apply (hasSubst_coordFamily hs c) (hasSubst_coordFamily hs d)]
  congr 1
  funext i
  exact subst_coordFamily_coordFamily hs c d i

theorem coordFamily_zero (s : ℕ) : coordFamily (n := n) s (0 : K) = X := by
  funext i
  unfold coordFamily
  split_ifs with hi
  · rw [hi]
  · simp

theorem subst_coordFamily_inv {s : ℕ} (hs : s ≠ 0) (c : K) (f : MvPowerSeries (Fin (n + 1)) K) :
    subst (coordFamily s (-c)) (subst (coordFamily s c) f) = f := by
  rw [subst_coordFamily_subst hs, add_neg_cancel, coordFamily_zero, subst_self]
  rfl

/-- The `K`-algebra automorphism `X 0 ↦ X 0`, `X i ↦ X i + X 0 ^ (s ^ i)` for `i ≠ 0`. -/
noncomputable def coordChange {s : ℕ} (hs : s ≠ 0) :
    MvPowerSeries (Fin (n + 1)) K ≃ₐ[K] MvPowerSeries (Fin (n + 1)) K :=
  AlgEquiv.ofAlgHom (substAlgHom (hasSubst_coordFamily hs 1))
    (substAlgHom (hasSubst_coordFamily hs (-1)))
    (AlgHom.ext fun f => by
      simpa using subst_coordFamily_inv hs (-1 : K) f)
    (AlgHom.ext fun f => by
      simpa using subst_coordFamily_inv hs (1 : K) f)

theorem coordChange_apply {s : ℕ} (hs : s ≠ 0) (f : MvPowerSeries (Fin (n + 1)) K) :
    coordChange hs f = subst (coordFamily s (1 : K)) f := by
  simp [coordChange]

/-- The substitution `X 0 ↦ X`, `X i ↦ 0` for `i ≠ 0`, into power series in one variable. -/
noncomputable def restrictFamily : Fin (n + 1) → MvPowerSeries Unit K :=
  fun i => if i = 0 then X () else 0

theorem hasSubst_restrictFamily : HasSubst (restrictFamily (K := K) (n := n)) :=
  hasSubst_of_constantCoeff_zero fun i => by
    unfold restrictFamily
    split_ifs <;> simp

theorem coeff_subst_restrictFamily (g : MvPowerSeries (Fin (n + 1)) K) (k : ℕ) :
    coeff (Finsupp.single () k) (subst restrictFamily g) = coeff (Finsupp.single 0 k) g := by
  classical
  rw [coeff_subst hasSubst_restrictFamily, finsum_eq_single _ (Finsupp.single 0 k)]
  · rw [Finsupp.prod_single_index (by simp)]
    simp [restrictFamily, coeff_X_pow]
  · intro d hd
    by_cases h : ∃ i, i ≠ 0 ∧ d i ≠ 0
    · obtain ⟨i, hi0, hi⟩ := h
      rw [Finsupp.prod, Finset.prod_eq_zero (i := i) (Finsupp.mem_support_iff.mpr hi)
        (by simp [restrictFamily, hi0, zero_pow hi])]
      simp
    · push Not at h
      have hd' : d = Finsupp.single 0 (d 0) := by
        ext i
        by_cases hi : i = 0
        · subst hi; simp
        · rw [h i hi, Finsupp.single_eq_of_ne hi]
      have hk : d 0 ≠ k := fun hk => hd (by rw [hd', hk])
      rw [hd', Finsupp.prod_single_index (by simp)]
      simp [restrictFamily, coeff_X_pow, hk.symm]

/-- The weight `∑ d i * s ^ i` of an exponent vector. -/
def expWeight (s : ℕ) (d : Fin (n + 1) →₀ ℕ) : ℕ :=
  ∑ i, d i * s ^ (i : ℕ)

/-- The substitution `X i ↦ X ^ (s ^ i)` into power series in one variable. -/
noncomputable def powFamily (s : ℕ) : Fin (n + 1) → MvPowerSeries Unit K :=
  fun i => X () ^ (s ^ (i : ℕ))

theorem hasSubst_powFamily {s : ℕ} (hs : s ≠ 0) : HasSubst (powFamily (K := K) (n := n) s) :=
  hasSubst_of_constantCoeff_zero fun i => by simp [powFamily, zero_pow (pow_ne_zero _ hs)]

theorem subst_restrictFamily_coordFamily {s : ℕ} (hs : s ≠ 0)
    (f : MvPowerSeries (Fin (n + 1)) K) :
    subst (restrictFamily (K := K)) (subst (coordFamily s (1 : K)) f) =
      subst (powFamily (K := K) s) f := by
  rw [subst_comp_subst_apply (hasSubst_coordFamily hs 1) hasSubst_restrictFamily]
  congr 1
  funext i
  have hr := hasSubst_restrictFamily (K := K) (n := n)
  by_cases hi : i = 0
  · rw [hi, coordFamily_apply_zero, subst_X hr]
    simp [restrictFamily, powFamily]
  · rw [coordFamily_apply_of_ne _ _ hi, subst_add hr, subst_smul hr, subst_pow hr, subst_X hr,
      subst_X hr]
    simp [restrictFamily, powFamily, hi]

theorem coeff_subst_powFamily {s : ℕ} (hs : s ≠ 0) (f : MvPowerSeries (Fin (n + 1)) K) (k : ℕ) :
    coeff (Finsupp.single () k) (subst (powFamily s) f) =
      ∑ᶠ d, coeff d f • (if expWeight s d = k then (1 : K) else 0) := by
  classical
  rw [coeff_subst (hasSubst_powFamily hs)]
  refine finsum_congr fun d => ?_
  congr 1
  rw [Finsupp.prod_fintype _ _ (by simp)]
  simp only [powFamily, ← pow_mul, Finset.prod_pow_eq_pow_sum, coeff_X_pow]
  have h : (∑ i : Fin (n + 1), s ^ (i : ℕ) * d i) = expWeight s d := by
    unfold expWeight
    exact Finset.sum_congr rfl fun i _ => mul_comm _ _
  rw [h]
  simp only [(Finsupp.single_injective ()).eq_iff]
  split_ifs <;> first | rfl | omega

end CoordinateChange

/-- A nonzero power series in `n + 1` variables becomes, after a `K`-algebra automorphism, a
series with a nonzero coefficient at some pure power `X 0 ^ k` of the first variable. -/
theorem exists_algEquiv_coeff_single_zero_ne_zero {K : Type*} [CommRing K] {n : ℕ}
    {f : MvPowerSeries (Fin (n + 1)) K} (hf : f ≠ 0) :
    ∃ φ : MvPowerSeries (Fin (n + 1)) K ≃ₐ[K] MvPowerSeries (Fin (n + 1)) K,
      ∃ k : ℕ, MvPowerSeries.coeff (Finsupp.single 0 k) (φ f) ≠ 0 := by
  classical
  obtain ⟨d₀, hd₀⟩ := (ne_zero_iff_exists_coeff_ne_zero f).mp hf
  obtain ⟨α, hα, hmin⟩ := (InvImage.wf (fun d : Fin (n + 1) →₀ ℕ => toColex (⇑d))
    wellFounded_lt).has_min {d | coeff d f ≠ 0} ⟨d₀, hd₀⟩
  set s := ∑ i, α i + 1 with hs_def
  have hs : s ≠ 0 := by omega
  have hαs : ∀ i, α i < s := fun i => by
    have := Finset.single_le_sum (f := fun i => α i) (fun _ _ => Nat.zero_le _)
      (Finset.mem_univ i)
    omega
  refine ⟨coordChange hs, expWeight s α, ?_⟩
  rw [← coeff_subst_restrictFamily, coordChange_apply, subst_restrictFamily_coordFamily hs,
    coeff_subst_powFamily hs, finsum_eq_single _ α]
  · simpa using hα
  · intro d hd
    by_cases hdf : coeff d f = 0
    · simp [hdf]
    · have hlt : toColex (⇑α) < toColex (⇑d) := by
        rcases lt_trichotomy (toColex (⇑α)) (toColex (⇑d)) with h | h | h
        · exact h
        · exact absurd (DFunLike.coe_injective (toColex.injective h)).symm hd
        · exact absurd h (hmin d hdf)
      have := sum_mul_pow_lt_of_colex s (⇑α) (⇑d) hαs hlt
      have hne : expWeight s d ≠ expWeight s α := by unfold expWeight; omega
      simp [hne]

end Langlands.CommutativeAlgebra.MvPowerSeriesFactorial
