import Langlands.HarmonicAnalysis.HarishChandraSchwartz.ConstantTermBound
import Langlands.HarmonicAnalysis.HarishChandraSchwartz.Height

/-! # Lemma II.3.1: `1 + σ(m u) ≍ 1 + sup(σ(m), σ(u))`

Waldspurger 2003, Lemma II.3.1: for a semi-standard `P = M U` there are `C₁, C₂ > 0` with
`C₁ (1 + σ(m u)) ≤ 1 + sup(σ(m), σ(u)) ≤ C₂ (1 + σ(m u))`. The first inequality is
subadditivity. For the second, Waldspurger conjugates the embedding `τ` so that `τ(M)` is
block diagonal and `τ(U)` block upper unitriangular for a block decomposition of `n`;
then the entries of `τ(m)` are entries of `τ(m u)`, so `σ(m) ≤ σ(m u)`, and
`σ(u) ≤ σ(m⁻¹) + σ(m u)` finishes the proof. This module proves the matrix fact for the
height `height τ` of `Height`, the deduction for any `σ` with `σ(m) ≤ σ(m u)`, and the
invariance of the conclusion under conjugating `τ`. The block form itself is a hypothesis.
-/

noncomputable section

open Matrix

namespace Langlands.HarishChandraSchwartz

universe u v w

section Blocks

variable {F : Type v} [NormedField F] {ι : Type w} [Fintype ι] [DecidableEq ι]
  {β : Type*} [LinearOrder β] (b : ι → β)

/-- `A` is block diagonal for the blocks `b⁻¹(β)`: `A i j = 0` unless `b i = b j`. -/
def IsBlockDiagonal (A : Matrix ι ι F) : Prop :=
  ∀ i j, b i ≠ b j → A i j = 0

/-- `A` is block upper unitriangular for the ordered blocks `b⁻¹(β)`: `A i j = δ_{ij}`
whenever `b j ≤ b i` (the identity on the diagonal blocks, zero below them). -/
def IsBlockUnipotent (A : Matrix ι ι F) : Prop :=
  ∀ i j, b j ≤ b i → A i j = if i = j then 1 else 0

variable {b}

/-- On the diagonal blocks, `A N = A` for `A` block diagonal and `N` block unipotent. -/
theorem IsBlockDiagonal.mul_apply {A N : Matrix ι ι F} (hA : IsBlockDiagonal b A)
    (hN : IsBlockUnipotent b N) {i j : ι} (hij : b i = b j) : (A * N) i j = A i j := by
  rw [Matrix.mul_apply, Finset.sum_eq_single j]
  · rw [hN j j le_rfl, ite_eq_left_iff.mpr (fun h => absurd rfl h), mul_one]
  · intro k _ hkj
    by_cases hk : b i = b k
    · rw [hN k j (hij ▸ hk ▸ le_rfl), ite_eq_right_iff.mpr (fun h => absurd h hkj), mul_zero]
    · rw [hA i k hk, zero_mul]
  · intro h
    exact absurd (Finset.mem_univ j) h

/-- On the diagonal blocks, `N A = A` for `N` block unipotent and `A` block diagonal. -/
theorem IsBlockDiagonal.mul_apply' {A N : Matrix ι ι F} (hA : IsBlockDiagonal b A)
    (hN : IsBlockUnipotent b N) {i j : ι} (hij : b i = b j) : (N * A) i j = A i j := by
  rw [Matrix.mul_apply, Finset.sum_eq_single i]
  · rw [hN i i le_rfl, ite_eq_left_iff.mpr (fun h => absurd rfl h), one_mul]
  · intro k _ hki
    by_cases hk : b k = b j
    · rw [hN i k (hk ▸ hij ▸ le_rfl), ite_eq_right_iff.mpr (fun h => absurd h (Ne.symm hki)), zero_mul]
    · rw [hA k j hk, mul_zero]
  · intro h
    exact absurd (Finset.mem_univ i) h

variable [Nonempty ι]

theorem IsBlockDiagonal.entryNorm_le_mul {A N : Matrix ι ι F} (hA : IsBlockDiagonal b A)
    (hN : IsBlockUnipotent b N) : entryNorm A ≤ entryNorm (A * N) := by
  refine entryNorm_le fun i j => ?_
  by_cases hij : b i = b j
  · rw [← hA.mul_apply hN hij]
    exact norm_le_entryNorm _ i j
  · rw [hA i j hij, norm_zero]
    exact entryNorm_nonneg _

theorem IsBlockDiagonal.entryNorm_le_mul' {A N : Matrix ι ι F} (hA : IsBlockDiagonal b A)
    (hN : IsBlockUnipotent b N) : entryNorm A ≤ entryNorm (N * A) := by
  refine entryNorm_le fun i j => ?_
  by_cases hij : b i = b j
  · rw [← hA.mul_apply' hN hij]
    exact norm_le_entryNorm _ i j
  · rw [hA i j hij, norm_zero]
    exact entryNorm_nonneg _

/-- `‖m‖ ≤ ‖m u‖` for `m` block diagonal and `u` block unipotent, when `m⁻¹` is block
diagonal and `u⁻¹` block unipotent as well. -/
theorem glNorm_le_glNorm_mul {m n : GL ι F} (hm : IsBlockDiagonal b (m : Matrix ι ι F))
    (hm' : IsBlockDiagonal b ((m⁻¹ : GL ι F) : Matrix ι ι F))
    (hn : IsBlockUnipotent b (n : Matrix ι ι F))
    (hn' : IsBlockUnipotent b ((n⁻¹ : GL ι F) : Matrix ι ι F)) :
    glNorm m ≤ glNorm (m * n) := by
  refine max_le ?_ ?_
  · calc entryNorm (m : Matrix ι ι F) ≤ entryNorm ((m : Matrix ι ι F) * (n : Matrix ι ι F)) :=
          hm.entryNorm_le_mul hn
      _ ≤ glNorm (m * n) := by
          rw [← Units.val_mul]
          exact le_max_left _ _
  · calc entryNorm ((m⁻¹ : GL ι F) : Matrix ι ι F)
        ≤ entryNorm (((n⁻¹ : GL ι F) : Matrix ι ι F) * ((m⁻¹ : GL ι F) : Matrix ι ι F)) :=
          hm'.entryNorm_le_mul' hn'
      _ ≤ glNorm (m * n) := by
          rw [← Units.val_mul, ← _root_.mul_inv_rev]
          exact le_max_right _ _

end Blocks

section Deduction

variable {G : Type u} [Group G] {M U : Subgroup G}

variable (M U) in
/-- The first inequality of Lemma II.3.1, from subadditivity:
`1 + σ(m u) ≤ 2 (1 + sup(σ(m), σ(u)))`. -/
theorem one_add_mul_le_two_mul (σ : G → ℝ) (hσ : ∀ g, 0 ≤ σ g)
    (hsub : ∀ x y, σ (x * y) ≤ σ x + σ y) (m : M) (u : U) :
    1 + σ ((m : G) * u) ≤ 2 * (1 + max (σ m) (σ u)) := by
  have h := hsub (m : G) u
  have h1 := le_max_left (σ m) (σ u)
  have h2 := le_max_right (σ m) (σ u)
  have := hσ m
  linarith

/-- The second inequality of Lemma II.3.1 from `σ(m) ≤ σ(m u)`: with subadditivity and
`σ(g⁻¹) = σ(g)`, `sup(σ(m), σ(u)) ≤ 2 σ(m u)`, so `SigmaProductBound M U σ` holds with
`C = 1/2`. -/
theorem sigmaProductBound_of_le_mul {σ : G → ℝ} (hσ : ∀ g, 0 ≤ σ g)
    (hsub : ∀ x y, σ (x * y) ≤ σ x + σ y) (hinv : ∀ g, σ g⁻¹ = σ g)
    (hle : ∀ m : M, ∀ u : U, σ m ≤ σ ((m : G) * u)) : SigmaProductBound M U σ := by
  refine ⟨1 / 2, by norm_num, fun m u => ?_⟩
  have h1 := hle m u
  have h2 : σ u ≤ σ m + σ ((m : G) * u) := by
    have := hsub (m : G)⁻¹ ((m : G) * u)
    rwa [inv_mul_cancel_left, hinv] at this
  have hmax : max (σ m) (σ u) ≤ 2 * σ ((m : G) * u) := by
    have := hσ ((m : G) * u)
    rcases le_total (σ u) (2 * σ m) with h | h
    · exact max_le (by linarith) (by linarith)
    · exact max_le (by linarith) (by linarith)
  have := hσ ((m : G) * u)
  linarith

/-- The conclusion of Lemma II.3.1 is unchanged, up to the constant, by a bounded change
of `σ`: if `σ ≤ σ' + c` and `σ' ≤ σ + c` with `c ≥ 0`, `σ, σ' ≥ 0`, then
`SigmaProductBound M U σ'` implies `SigmaProductBound M U σ`. -/
theorem SigmaProductBound.of_le_add {σ σ' : G → ℝ} (h : SigmaProductBound M U σ')
    (hσ : ∀ g, 0 ≤ σ g) (hσ' : ∀ g, 0 ≤ σ' g) {c : ℝ} (hc : 0 ≤ c)
    (h₁ : ∀ g, σ g ≤ σ' g + c) (h₂ : ∀ g, σ' g ≤ σ g + c) : SigmaProductBound M U σ := by
  obtain ⟨C, hC, h⟩ := h
  refine ⟨C / (1 + c) ^ 2, by positivity, fun m u => ?_⟩
  have hmax : 1 + max (σ m) (σ u) ≤ (1 + c) * (1 + max (σ' m) (σ' u)) := by
    have hA : max (σ m) (σ u) ≤ max (σ' m) (σ' u) + c :=
      max_le ((h₁ m).trans (by linarith [le_max_left (σ' m) (σ' u)]))
        ((h₁ u).trans (by linarith [le_max_right (σ' m) (σ' u)]))
    have hB : 0 ≤ max (σ' m) (σ' u) := (hσ' m).trans (le_max_left _ _)
    nlinarith
  have hmu := h m u
  have hmu' := h₂ ((m : G) * u)
  have hσmu := hσ ((m : G) * u)
  have hpos : 0 < 1 + c := by linarith
  rw [div_mul_eq_mul_div, div_le_iff₀ (by positivity)]
  calc C * (1 + max (σ m) (σ u)) ≤ C * ((1 + c) * (1 + max (σ' m) (σ' u))) :=
        mul_le_mul_of_nonneg_left hmax hC.le
    _ = (1 + c) * (C * (1 + max (σ' m) (σ' u))) := by ring
    _ ≤ (1 + c) * (1 + σ' ((m : G) * u)) := mul_le_mul_of_nonneg_left hmu hpos.le
    _ ≤ (1 + c) * ((1 + c) * (1 + σ ((m : G) * u))) := by
        refine mul_le_mul_of_nonneg_left ?_ hpos.le
        nlinarith
    _ = (1 + σ ((m : G) * u)) * (1 + c) ^ 2 := by ring

end Deduction

section HeightFunction

variable {G : Type u} [Group G] {M U : Subgroup G}
variable {F : Type v} [NormedField F] [IsUltrametricDist F] {ι : Type w} [Fintype ι]
  [DecidableEq ι] [Nonempty ι]

/-- Conjugating `τ` by `x ∈ GL ι F` changes the height by at most
`c = log (‖x‖ ‖x⁻¹‖)`. -/
theorem height_conj_le (τ : G →* GL ι F) (x : GL ι F) (g : G) :
    height ((MulAut.conj x).toMonoidHom.comp τ) g ≤
      height τ g + Real.log (glNorm x * glNorm x⁻¹) := by
  unfold height
  simp only [MonoidHom.coe_comp, MulEquiv.coe_toMonoidHom, Function.comp_apply,
    MulAut.conj_apply]
  rw [← Real.log_mul (glNorm_pos _).ne' (mul_pos (glNorm_pos _) (glNorm_pos _)).ne']
  refine Real.log_le_log (glNorm_pos _) ?_
  calc glNorm (x * τ g * x⁻¹) ≤ glNorm (x * τ g) * glNorm x⁻¹ := glNorm_mul_le _ _
    _ ≤ glNorm x * glNorm (τ g) * glNorm x⁻¹ := by
        gcongr
        · exact (glNorm_pos _).le
        · exact glNorm_mul_le _ _
    _ = glNorm (τ g) * (glNorm x * glNorm x⁻¹) := by ring

/-- Waldspurger, Lemma II.3.1 for the height `σ = height τ`: if, after conjugation by some
`x ∈ GL ι F`, `τ(M)` is block diagonal and `τ(U)` block upper unitriangular for one
ordered block decomposition `b`, then `SigmaProductBound M U (height τ)`. -/
theorem sigmaProductBound_height (τ : G →* GL ι F) (x : GL ι F) {β : Type*} [LinearOrder β]
    (b : ι → β)
    (hM : ∀ m ∈ M, IsBlockDiagonal b ((x * τ m * x⁻¹ : GL ι F) : Matrix ι ι F))
    (hU : ∀ u ∈ U, IsBlockUnipotent b ((x * τ u * x⁻¹ : GL ι F) : Matrix ι ι F)) :
    SigmaProductBound M U (height τ) := by
  set τ' := (MulAut.conj x).toMonoidHom.comp τ
  have hτ' : ∀ g, τ' g = x * τ g * x⁻¹ := fun g => by
    simp only [τ', MonoidHom.coe_comp, MulEquiv.coe_toMonoidHom, Function.comp_apply,
      MulAut.conj_apply]
  have h' : SigmaProductBound M U (height τ') := by
    refine sigmaProductBound_of_le_mul (height_nonneg τ') (height_mul_le τ')
      (height_inv τ') fun m u => ?_
    unfold height
    rw [map_mul]
    refine Real.log_le_log (glNorm_pos _) (glNorm_le_glNorm_mul (b := b) ?_ ?_ ?_ ?_)
    · rw [hτ']
      exact hM m m.2
    · rw [← map_inv, hτ']
      exact hM _ (M.inv_mem m.2)
    · rw [hτ']
      exact hU u u.2
    · rw [← map_inv, hτ']
      exact hU _ (U.inv_mem u.2)
  set c := Real.log (glNorm x * glNorm x⁻¹)
  have hc : 0 ≤ c := Real.log_nonneg (by
    have h1 := one_le_glNorm x
    have h2 := one_le_glNorm x⁻¹
    nlinarith)
  refine h'.of_le_add (height_nonneg τ) (height_nonneg τ') hc (fun g => ?_)
    (fun g => height_conj_le τ x g)
  -- `τ = conj(x⁻¹) ∘ τ'`
  have h := height_conj_le τ' x⁻¹ g
  have hτ'' : (MulAut.conj x⁻¹).toMonoidHom.comp τ' = τ := by
    ext g
    simp only [τ', MonoidHom.coe_comp, MulEquiv.coe_toMonoidHom, Function.comp_apply,
      MulAut.conj_apply]
    group
  rw [hτ'', inv_inv, mul_comm (glNorm x⁻¹)] at h
  exact h

end HeightFunction

end Langlands.HarishChandraSchwartz
