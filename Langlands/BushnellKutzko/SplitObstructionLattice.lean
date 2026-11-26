import Langlands.BushnellKutzko.RadicalFiltrationProof
import Langlands.BushnellKutzko.CorestrictionLatticeDual
import Langlands.BushnellKutzko.AdjointLatticeBounds
import Langlands.AnthropicFLT.Theorems.Thm_IsAdicComplete_of_finite_of_isNoetherianRing

/-! # Separation, completeness and off-diagonal blocks of the endomorphism filtration

For an `𝔬_F`-lattice chain `𝓛` in a vector space over a nonarchimedean local field `F`, the
filtration `𝔓^n = End^n_{𝔬_F}(𝓛)` of `A = End_F(V)` is exhaustive and separated, and it is
complete: a sequence whose successive differences go deeper and deeper in the filtration has a
limit. For two complementary idempotents `ε₁, ε₂` of the order, the off-diagonal block
`ε₁ A ε₂` inherits a filtration, and a map which is surjective on each graded step of that
filtration is surjective on every filtration step (Nakayama's lemma).
-/

noncomputable section

open ValuativeRel
open scoped Pointwise

namespace Langlands.BushnellKutzko.SplitObstruction

universe uF uV

variable {F : Type uF} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F] {V : Type uV} [AddCommGroup V] [Module F V]
  (𝓛 : LatticeChain 𝒪[F] F V)

local notation "P" => 𝓛.endFiltration
local notation "A" => Module.End F V

/-- Every endomorphism lies in some step of the filtration. -/
theorem exists_mem_endFiltration (x : A) : ∃ k : ℤ, x ∈ P k := by
  by_cases hx : x = 0
  · exact ⟨0, hx ▸ zero_mem _⟩
  · exact ((radicalFiltration F V 𝓛).2.2.2.2 x hx).1

/-- An endomorphism lying in every step of the filtration is zero. -/
theorem eq_zero_of_forall_mem {x : A} (h : ∀ k : ℤ, x ∈ P k) : x = 0 := by
  by_contra hx
  obtain ⟨N, hN⟩ := ((radicalFiltration F V 𝓛).2.2.2.2 x hx).2
  have := hN (h (N + 1))
  omega

/-- An endomorphism lying in all sufficiently deep steps of the filtration is zero. -/
theorem eq_zero_of_forall_ge_mem {x : A} {k₀ : ℤ} (h : ∀ k : ℕ, x ∈ P (k₀ + k)) : x = 0 := by
  apply eq_zero_of_forall_mem 𝓛
  intro k
  by_cases hk : k ≤ k₀
  · exact 𝓛.endFiltration_antitone hk (by simpa using h 0)
  · have := h (k - k₀).toNat
    rwa [Int.toNat_of_nonneg (by omega), add_sub_cancel] at this

omit [TopologicalSpace F] [IsNonarchimedeanLocalField F] in
/-- Telescoping differences of a sequence. -/
theorem telescope_mem {c : ℤ} (f : ℕ → A) (hf : ∀ k : ℕ, f (k + 1) - f k ∈ P (c + k))
    (k m : ℕ) : f (k + m) - f k ∈ P (c + k) := by
  induction m with
  | zero => simp
  | succ m ih =>
    have h := hf (k + m)
    have h' : f (k + m + 1) - f (k + m) ∈ P (c + k) :=
      𝓛.endFiltration_antitone (by push_cast; omega) h
    have hsum := add_mem ih h'
    rw [show k + (m + 1) = k + m + 1 by omega]
    rwa [sub_add_sub_cancel'] at hsum

/-- Completeness of the filtration: a sequence in `𝔓^c` whose `k`-th difference lies in
`𝔓^{c+k}` has a limit `L ∈ 𝔓^c` with `L − f k ∈ 𝔓^{c+k}` for all `k`. -/
theorem exists_limit {c : ℤ} (f : ℕ → A) (hf0 : ∀ k, f k ∈ P c)
    (hf : ∀ k : ℕ, f (k + 1) - f k ∈ P (c + k)) :
    ∃ L ∈ P c, ∀ k : ℕ, L - f k ∈ P (c + k) := by
  classical
  let : UniformSpace F := IsTopologicalAddGroup.rightUniformSpace F
  have : IsUniformAddGroup F := isUniformAddGroup_of_addCommGroup
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible 𝒪[F]
  have hϖ0 : (ϖ : F) ≠ 0 := fun h => hϖ.ne_zero (Subtype.ext h)
  let M := P c
  have : Module.Finite 𝒪[F] M := Module.Finite.iff_fg.mpr (𝓛.fg_endFiltration c)
  have : IsAdicComplete 𝓂[F] M := IsAdicComplete.of_finite_of_isNoetherianRing 𝓂[F] M
  set e : ℕ := 𝓛.period with he
  have hmem : ∀ (n : ℕ) (y : M),
      y ∈ (𝓂[F] ^ n • ⊤ : Submodule 𝒪[F] M) ↔ (y : A) ∈ P (c + n * e) := by
    intro n y
    rw [hϖ.maximalIdeal_eq, Ideal.span_singleton_pow, Submodule.ideal_span_singleton_smul,
      Submodule.mem_smul_pointwise_iff_exists]
    constructor
    · rintro ⟨z, -, rfl⟩
      have h := (𝓛.uniformizer_pow_end_mem_iff hϖ n c (z : A)).2 z.2
      convert h using 1
    · intro hy
      let w : A := ((ϖ : F) ^ n)⁻¹ • (y : A)
      have hw : (ϖ : F) ^ n • w = y := by
        simp only [w, smul_smul, mul_inv_cancel₀ (pow_ne_zero n hϖ0), one_smul]
      have hwc : w ∈ M := (𝓛.uniformizer_pow_end_mem_iff hϖ n c w).1 (by rw [hw]; exact hy)
      refine ⟨⟨w, hwc⟩, Submodule.mem_top, ?_⟩
      apply Subtype.ext
      change (ϖ ^ n : 𝒪[F]) • w = (y : A)
      rw [← algebraMap_smul F (ϖ ^ n) w]
      exact hw
  let g : ℕ → M := fun n => ⟨f (n * e), hf0 _⟩
  have hg : ∀ {m n : ℕ}, m ≤ n → g m ≡ g n [SMOD (𝓂[F] ^ m • ⊤ : Submodule 𝒪[F] M)] := by
    intro m n hmn
    rw [SModEq.sub_mem, hmem]
    obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hmn
    have h := telescope_mem 𝓛 f hf (m * e) (d * e)
    have h' := neg_mem h
    rw [neg_sub] at h'
    change f (m * e) - f ((m + d) * e) ∈ _
    rw [show (m + d) * e = m * e + d * e by ring]
    push_cast at h' ⊢
    exact h'
  obtain ⟨L, hL⟩ := IsPrecomplete.prec inferInstance hg
  refine ⟨L, L.2, fun k => ?_⟩
  have hk := hL k
  rw [SModEq.sub_mem, hmem] at hk
  change f (k * e) - (L : A) ∈ _ at hk
  have hk' : (L : A) - f (k * e) ∈ P (c + k) := by
    have h := neg_mem hk
    rw [neg_sub] at h
    have hke : (k : ℤ) ≤ k * e := by
      have : 1 ≤ e := 𝓛.period_pos
      have : (1 : ℤ) ≤ e := by exact_mod_cast this
      nlinarith
    exact 𝓛.endFiltration_antitone (by omega) h
  have hd : f (k * e) - f k ∈ P (c + k) := by
    obtain ⟨d, hd⟩ : ∃ d, k * e = k + d := ⟨k * e - k, by
      have : k ≤ k * e := Nat.le_mul_of_pos_right k 𝓛.period_pos
      omega⟩
    rw [hd]
    exact telescope_mem 𝓛 f hf k d
  have := add_mem hk' hd
  rwa [sub_add_sub_cancel] at this

section Blocks

/-- The off-diagonal block `ε₁ A ε₂ = {x : ε₁ x ε₂ = x}` of `A`. -/
def offDiagonal (ε₁ ε₂ : A) : Submodule F A where
  carrier := {x | ε₁ * x * ε₂ = x}
  add_mem' := by
    intro x y hx hy
    change ε₁ * (x + y) * ε₂ = x + y
    rw [mul_add, add_mul]
    change ε₁ * x * ε₂ = x at hx
    change ε₁ * y * ε₂ = y at hy
    rw [hx, hy]
  zero_mem' := by
    change ε₁ * 0 * ε₂ = 0
    simp
  smul_mem' := by
    intro t x hx
    change ε₁ * (t • x) * ε₂ = t • x
    change ε₁ * x * ε₂ = x at hx
    rw [mul_smul_comm, smul_mul_assoc, hx]

omit [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] in
theorem mem_offDiagonal (ε₁ ε₂ : A) {x : A} : x ∈ offDiagonal ε₁ ε₂ ↔ ε₁ * x * ε₂ = x :=
  Iff.rfl

/-- The filtration `𝔓^i ∩ ε₁ A ε₂` of the off-diagonal block. -/
def blockFiltration (𝓛 : LatticeChain 𝒪[F] F V) (ε₁ ε₂ : A) (i : ℤ) : Submodule 𝒪[F] A :=
  𝓛.endFiltration i ⊓ (offDiagonal ε₁ ε₂).restrictScalars 𝒪[F]

omit [TopologicalSpace F] [IsNonarchimedeanLocalField F] in
theorem mem_blockFiltration (ε₁ ε₂ : A) {i : ℤ} {x : A} :
    x ∈ blockFiltration 𝓛 ε₁ ε₂ i ↔ x ∈ P i ∧ ε₁ * x * ε₂ = x :=
  Iff.rfl

omit [TopologicalSpace F] [IsNonarchimedeanLocalField F] in
theorem blockFiltration_antitone (ε₁ ε₂ : A) : Antitone (blockFiltration 𝓛 ε₁ ε₂) := by
  intro i j hij x hx
  exact ⟨𝓛.endFiltration_antitone hij hx.1, hx.2⟩

/-- Graded surjectivity on the block filtration implies surjectivity on every step, by
Nakayama's lemma over `𝔬_F`. -/
theorem blockFiltration_surjective (ε₁ ε₂ : A) {D : A →ₗ[F] A} {r : ℤ}
    (h : ∀ i : ℤ, ∀ y ∈ blockFiltration 𝓛 ε₁ ε₂ (i - r),
      ∃ x ∈ blockFiltration 𝓛 ε₁ ε₂ i, y - D x ∈ blockFiltration 𝓛 ε₁ ε₂ (i + 1 - r))
    (j : ℤ) : ∀ y ∈ blockFiltration 𝓛 ε₁ ε₂ (j - r),
      ∃ x ∈ blockFiltration 𝓛 ε₁ ε₂ j, D x = y := by
  classical
  set M := blockFiltration 𝓛 ε₁ ε₂ with hM
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible 𝒪[F]
  have hϖ0 : (ϖ : F) ≠ 0 := fun h => hϖ.ne_zero (Subtype.ext h)
  -- iterate the graded statement
  have hiter : ∀ k : ℕ, ∀ y ∈ M (j - r), ∃ x ∈ M j, y - D x ∈ M (j - r + k) := by
    intro k
    induction k with
    | zero =>
      intro y hy
      exact ⟨0, zero_mem _, by simpa using hy⟩
    | succ k ih =>
      intro y hy
      obtain ⟨x, hx, hyx⟩ := ih y hy
      have hyx' : y - D x ∈ M ((j + k) - r) := by
        rw [show j + k - r = j - r + k by ring]
        exact hyx
      obtain ⟨x', hx', hyx''⟩ := h (j + k) (y - D x) hyx'
      refine ⟨x + x', add_mem hx (blockFiltration_antitone 𝓛 ε₁ ε₂ (by omega) hx'), ?_⟩
      rw [map_add, ← sub_sub]
      convert hyx'' using 2
      push_cast
      ring
  -- the image submodule
  let N : Submodule 𝒪[F] A := (M j).map (D.restrictScalars 𝒪[F])
  have hFG : (M (j - r)).FG := Submodule.FG.of_le (𝓛.fg_endFiltration (j - r)) inf_le_left
  have hle : M (j - r) ≤ N ⊔ 𝓂[F] • M (j - r) := by
    intro y hy
    obtain ⟨x, hx, hyx⟩ := hiter 𝓛.period y hy
    rw [Submodule.mem_sup]
    refine ⟨D x, ⟨x, hx, rfl⟩, y - D x, ?_, by abel⟩
    -- `y - D x ∈ 𝔓^{j-r+e} ∩ ε₁Aε₂ = ϖ (𝔓^{j-r} ∩ ε₁Aε₂)`
    obtain ⟨hyx1, hyx2⟩ := hyx
    let w : A := (ϖ : F)⁻¹ • (y - D x)
    have hw : (ϖ : F) • w = y - D x := by
      simp only [w, smul_smul, mul_inv_cancel₀ hϖ0, one_smul]
    have hw1 : w ∈ P (j - r) := (𝓛.uniformizer_end_mem_iff hϖ (j - r) w).1 (by rw [hw]; exact hyx1)
    have hw2 : ε₁ * w * ε₂ = w := by
      change ε₁ * (y - D x) * ε₂ = y - D x at hyx2
      simp only [w, mul_smul_comm, smul_mul_assoc, hyx2]
    have hwM : w ∈ M (j - r) := ⟨hw1, hw2⟩
    rw [hϖ.maximalIdeal_eq, Submodule.ideal_span_singleton_smul]
    refine Submodule.mem_smul_pointwise_iff_exists _ _ _ |>.mpr ⟨w, hwM, ?_⟩
    rw [← hw, ← algebraMap_smul F ϖ w]
    rfl
  have hjac : 𝓂[F] ≤ (⊥ : Ideal 𝒪[F]).jacobson := by
    rw [Ideal.jacobson_bot, IsLocalRing.ringJacobson_eq_maximalIdeal]
  have hNak := Submodule.le_of_le_smul_of_le_jacobson_bot hFG hjac hle
  intro y hy
  obtain ⟨x, hx, hxy⟩ := hNak hy
  exact ⟨x, hx, hxy⟩

end Blocks

end Langlands.BushnellKutzko.SplitObstruction
