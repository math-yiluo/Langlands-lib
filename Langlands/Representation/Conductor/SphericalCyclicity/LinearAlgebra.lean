import Mathlib

/-!
# A finite-dimensional cyclicity lemma for an upper-triangular cell operator

The operator `cellMatrix r q z` records how a Hecke-type finite sum of translates
acts on the values of parahoric-invariant vectors at the `r` cell representatives.
Every subspace that contains the all-ones vector and is stable under it is the
whole space, provided the norms of `z` are weakly increasing.
-/

noncomputable section

namespace Langlands.Conductor.SphericalCyclicity

open Module
open scoped BigOperators

/-- The upper-triangular matrix
`M j i = (z j * q^(j+1))⁻¹ * (q^(j+1) [j = i] + (q - 1) q^i [j < i])`. -/
def cellMatrix (r q : ℕ) (z : Fin r → ℂ) : Matrix (Fin r) (Fin r) ℂ :=
  fun j i => (z j * (q : ℂ) ^ ((j : ℕ) + 1))⁻¹ *
    (if j = i then (q : ℂ) ^ ((j : ℕ) + 1)
      else if j < i then ((q : ℂ) - 1) * (q : ℂ) ^ (i : ℕ) else 0)

private theorem sum_filter_lt_succ {r : ℕ} (f : Fin r → ℂ) (k : ℕ) (hk : k < r) :
    ∑ j ∈ Finset.univ.filter (fun j : Fin r => (j : ℕ) < k + 1), f j =
      ∑ j ∈ Finset.univ.filter (fun j : Fin r => (j : ℕ) < k), f j + f ⟨k, hk⟩ := by
  have hset : Finset.univ.filter (fun j : Fin r => (j : ℕ) < k + 1) =
      insert ⟨k, hk⟩ (Finset.univ.filter (fun j : Fin r => (j : ℕ) < k)) := by
    ext j
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert, Fin.ext_iff]
    omega
  rw [hset, Finset.sum_insert (by simp), add_comm]

/-- If a subspace of `Fin r → ℂ` contains the all-ones vector and is stable under
`cellMatrix r q z`, with `2 ≤ q`, all `z i ≠ 0` and `‖z i‖` weakly increasing, then
it is the whole space. -/
theorem eq_top_of_cellMatrix_stable {r q : ℕ} (hq : 2 ≤ q) (z : Fin r → ℂ)
    (hz : ∀ i, z i ≠ 0) (hmono : Monotone fun i => ‖z i‖)
    (W : Submodule ℂ (Fin r → ℂ)) (hone : (fun _ => (1 : ℂ)) ∈ W)
    (hA : ∀ v ∈ W, (cellMatrix r q z).mulVec v ∈ W) : W = ⊤ := by
  by_contra hW
  set A : Module.End ℂ (Fin r → ℂ) := Matrix.mulVecLin (cellMatrix r q z) with hAdef
  have hmaps : ∀ ℓ ∈ W.dualAnnihilator,
      Module.Dual.transpose (R := ℂ) A ℓ ∈ W.dualAnnihilator := by
    intro ℓ hℓ
    rw [Submodule.mem_dualAnnihilator] at hℓ ⊢
    intro w hw
    rw [Module.Dual.transpose_apply, LinearMap.comp_apply]
    exact hℓ _ (hA w hw)
  have hN : W.dualAnnihilator ≠ ⊥ := by
    rwa [Ne, Submodule.dualAnnihilator_eq_bot_iff]
  have : Nontrivial W.dualAnnihilator := Submodule.nontrivial_iff_ne_bot.mpr hN
  obtain ⟨μ, hμ⟩ :=
    Module.End.exists_eigenvalue ((Module.Dual.transpose (R := ℂ) A).restrict hmaps)
  obtain ⟨ℓ, hℓ⟩ := hμ.exists_hasEigenvector
  have heig := hℓ.apply_eq_smul
  have hℓne : ℓ ≠ 0 := (Module.End.hasEigenvector_iff.mp hℓ).2
  set φ : Module.Dual ℂ (Fin r → ℂ) := ℓ.1 with hφ
  have hcomp : ∀ v, φ (A v) = μ * φ v := by
    intro v
    have := congrArg (fun ψ : W.dualAnnihilator => (ψ : Module.Dual ℂ (Fin r → ℂ)) v) heig
    simpa [LinearMap.restrict_apply, Module.Dual.transpose_apply] using this
  have hW0 : ∀ w ∈ W, φ w = 0 := (Submodule.mem_dualAnnihilator _).mp ℓ.2
  have hφne : φ ≠ 0 := by
    intro h
    apply hℓne
    exact Subtype.ext h
  -- coordinates of the functional
  set L : Fin r → ℂ := fun i => φ (fun j => if i = j then 1 else 0) with hL
  have hexp : ∀ v, φ v = ∑ i, v i * L i := by
    intro v
    rw [LinearMap.pi_apply_eq_sum_univ φ v]
    simp [hL, smul_eq_mul]
  have hqpos : (0 : ℝ) < q := by exact_mod_cast (show 0 < q by omega)
  have hq0 : (q : ℂ) ≠ 0 := by exact_mod_cast (show q ≠ 0 by omega)
  -- the normalized coordinates
  set ν : Fin r → ℂ := fun j => L j * (z j * (q : ℂ) ^ ((j : ℕ) + 1))⁻¹ with hν
  set P : ℕ → ℂ := fun k => ∑ j ∈ Finset.univ.filter (fun j : Fin r => (j : ℕ) < k), ν j
    with hP
  -- the eigen-equation at a basis vector
  have heqn : ∀ i : Fin r, (q : ℂ) ^ ((i : ℕ) + 1) * ν i +
      ((q : ℂ) - 1) * (q : ℂ) ^ (i : ℕ) * P i = μ * L i := by
    intro i
    have h1 := hcomp (fun j => if i = j then 1 else 0)
    rw [hexp, hexp] at h1
    have hlhs : ∑ j, A (fun j => if i = j then (1 : ℂ) else 0) j * L j =
        ∑ j, ν j * (if j = i then (q : ℂ) ^ ((j : ℕ) + 1)
          else if j < i then ((q : ℂ) - 1) * (q : ℂ) ^ (i : ℕ) else 0) := by
      apply Finset.sum_congr rfl
      intro j _
      have hAe : A (fun j => if i = j then (1 : ℂ) else 0) j = cellMatrix r q z j i := by
        rw [hAdef, Matrix.mulVecLin_apply, Matrix.mulVec, dotProduct]
        rw [Finset.sum_eq_single i]
        · simp
        · intro b _ hb
          simp [Ne.symm hb]
        · simp
      rw [hAe, cellMatrix, hν]
      ring
    rw [hlhs] at h1
    have hrhs : ∑ j, (if i = j then (1 : ℂ) else 0) * L j = L i := by
      rw [Finset.sum_eq_single i]
      · simp
      · intro b _ hb
        simp [Ne.symm hb]
      · simp
    rw [hrhs] at h1
    rw [← h1]
    have hsplit : ∑ j, ν j * (if j = i then (q : ℂ) ^ ((j : ℕ) + 1)
          else if j < i then ((q : ℂ) - 1) * (q : ℂ) ^ (i : ℕ) else 0) =
        ∑ j, ((if j = i then ν j * (q : ℂ) ^ ((j : ℕ) + 1) else 0) +
          (if j < i then ν j * (((q : ℂ) - 1) * (q : ℂ) ^ (i : ℕ)) else 0)) := by
      apply Finset.sum_congr rfl
      intro j _
      by_cases hji : j = i
      · subst hji
        simp
      · by_cases hlt : j < i
        · simp [hji, hlt]
        · simp [hji, hlt]
    rw [hsplit, Finset.sum_add_distrib, Finset.sum_ite_eq' Finset.univ i]
    simp only [Finset.mem_univ, ↓reduceIte]
    rw [← Finset.sum_filter, hP]
    simp only
    rw [← Finset.sum_mul]
    have hfilt : Finset.univ.filter (fun j : Fin r => j < i) =
        Finset.univ.filter (fun j : Fin r => (j : ℕ) < (i : ℕ)) := by
      ext j
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      exact Iff.rfl
    rw [hfilt]
    ring
  -- telescoping
  have htel : ∀ k, k ≤ r → (q : ℂ) ^ k * P k =
      μ * ∑ j ∈ Finset.univ.filter (fun j : Fin r => (j : ℕ) < k), L j := by
    intro k
    induction k with
    | zero =>
      intro _
      simp [hP]
    | succ k ih =>
      intro hk
      have hk' : k < r := by omega
      have hPk : P (k + 1) = P k + ν ⟨k, hk'⟩ := by
        simp only [hP]
        exact sum_filter_lt_succ ν k hk'
      rw [hPk, sum_filter_lt_succ L k hk', mul_add μ, ← ih (by omega)]
      have he := heqn ⟨k, hk'⟩
      simp only at he
      rw [← he]
      ring
  have hsumL : ∑ j, L j = 0 := by
    have := hW0 _ hone
    rw [hexp] at this
    simpa using this
  have hall : ∀ k, r ≤ k →
      Finset.univ.filter (fun j : Fin r => (j : ℕ) < k) = Finset.univ := by
    intro k hk
    ext j
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, iff_true]
    omega
  have hsumν : ∑ j, ν j = 0 := by
    have h := htel r le_rfl
    rw [hall r le_rfl] at h
    simp only [hP] at h
    rw [hall r le_rfl, hsumL, mul_zero] at h
    rcases mul_eq_zero.mp h with h' | h'
    · exact absurd h' (pow_ne_zero _ hq0)
    · exact h'
  -- the support of the functional
  have hLne : ∃ i, L i ≠ 0 := by
    by_contra hcon
    push Not at hcon
    apply hφne
    apply LinearMap.ext
    intro v
    rw [hexp]
    simp [hcon]
  set supp := Finset.univ.filter (fun i : Fin r => L i ≠ 0) with hsupp
  have hsuppne : supp.Nonempty := by
    obtain ⟨i, hi⟩ := hLne
    exact ⟨i, by simp [hsupp, hi]⟩
  set i0 := supp.min' hsuppne with hi0
  set k1 := supp.max' hsuppne with hk1
  have hi0mem : L i0 ≠ 0 := by
    have := supp.min'_mem hsuppne
    simpa [hsupp] using this
  have hk1mem : L k1 ≠ 0 := by
    have := supp.max'_mem hsuppne
    simpa [hsupp] using this
  have hbelow : ∀ j : Fin r, j < i0 → L j = 0 := by
    intro j hj
    by_contra hne
    have hmem : j ∈ supp := by simp [hsupp, hne]
    exact absurd (supp.min'_le j hmem) (not_le.mpr hj)
  have habove : ∀ j : Fin r, k1 < j → L j = 0 := by
    intro j hj
    by_contra hne
    have hmem : j ∈ supp := by simp [hsupp, hne]
    exact absurd (supp.le_max' j hmem) (not_le.mpr hj)
  have hi0k1 : i0 ≤ k1 := supp.min'_le k1 (supp.max'_mem hsuppne)
  have hzq : ∀ j : Fin r, z j * (q : ℂ) ^ ((j : ℕ) + 1) ≠ 0 :=
    fun j => mul_ne_zero (hz j) (pow_ne_zero _ hq0)
  -- the equation at the first support index
  have hP0 : P i0 = 0 := by
    simp only [hP]
    apply Finset.sum_eq_zero
    intro j hj
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hj
    simp [hν, hbelow j (Fin.lt_def.mpr hj)]
  have hμi0 : μ * z i0 = 1 := by
    have he := heqn i0
    rw [hP0, mul_zero, add_zero, hν] at he
    simp only at he
    have hcancel : (q : ℂ) ^ ((i0 : ℕ) + 1) * (L i0 * (z i0 * (q : ℂ) ^ ((i0 : ℕ) + 1))⁻¹) =
        L i0 * (z i0)⁻¹ := by
      field_simp
    rw [hcancel] at he
    have : L i0 * (z i0)⁻¹ * z i0 = μ * L i0 * z i0 := by rw [he]
    rw [inv_mul_cancel_right₀ (hz i0)] at this
    have h2 : L i0 * 1 = L i0 * (μ * z i0) := by rw [mul_one]; linear_combination this
    exact (mul_left_cancel₀ hi0mem h2).symm
  -- the equation at the last support index
  have hPk1 : P k1 = -ν k1 := by
    have hfull : ∑ j, ν j = P ((k1 : ℕ) + 1) := by
      simp only [hP]
      rw [← Finset.sum_filter_add_sum_filter_not Finset.univ
        (fun j : Fin r => (j : ℕ) < (k1 : ℕ) + 1)]
      rw [Finset.sum_eq_zero (s := Finset.univ.filter
        (fun j : Fin r => ¬ (j : ℕ) < (k1 : ℕ) + 1)), add_zero]
      intro j hj
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, not_lt] at hj
      have hlt : k1 < j := Fin.lt_def.mpr (by omega)
      simp [hν, habove j hlt]
    have h2 : P ((k1 : ℕ) + 1) = P k1 + ν k1 := by
      simp only [hP]
      exact sum_filter_lt_succ ν k1 k1.isLt
    rw [hsumν, h2] at hfull
    linear_combination -hfull
  have hμk1 : μ * ((q : ℂ) * z k1) = 1 := by
    have he := heqn k1
    rw [hPk1] at he
    have hνk1 : ν k1 * (z k1 * (q : ℂ) ^ ((k1 : ℕ) + 1)) = L k1 := by
      simp only [hν]
      rw [inv_mul_cancel_right₀ (hzq k1)]
    have hνne : ν k1 ≠ 0 := by
      intro h0
      rw [h0, zero_mul] at hνk1
      exact hk1mem hνk1.symm
    have h3 : ν k1 * (q : ℂ) ^ (k1 : ℕ) = ν k1 * ((q : ℂ) ^ (k1 : ℕ) * (μ * ((q : ℂ) * z k1))) := by
      rw [← hνk1] at he
      linear_combination he
    have h4 := mul_left_cancel₀ hνne h3
    have h5 : (q : ℂ) ^ (k1 : ℕ) * 1 = (q : ℂ) ^ (k1 : ℕ) * (μ * ((q : ℂ) * z k1)) := by
      rw [mul_one]; exact h4
    exact (mul_left_cancel₀ (pow_ne_zero _ hq0) h5).symm
  -- comparison of norms
  have hμne : μ ≠ 0 := by
    intro h0
    rw [h0, zero_mul] at hμi0
    exact zero_ne_one hμi0
  have hzrel : z i0 = (q : ℂ) * z k1 := by
    apply mul_left_cancel₀ hμne
    rw [hμi0, hμk1]
  have hnorm : ‖z i0‖ = (q : ℝ) * ‖z k1‖ := by
    rw [hzrel, norm_mul, Complex.norm_natCast]
  have hle : ‖z i0‖ ≤ ‖z k1‖ := hmono hi0k1
  have hpos : 0 < ‖z k1‖ := norm_pos_iff.mpr (hz k1)
  have hq2 : (2 : ℝ) ≤ q := by exact_mod_cast hq
  nlinarith

end Langlands.Conductor.SphericalCyclicity
