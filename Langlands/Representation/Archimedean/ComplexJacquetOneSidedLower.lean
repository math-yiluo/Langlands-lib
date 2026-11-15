import Langlands.Representation.Archimedean.ComplexJacquetOneSided

/-!
# One-sided nonvanishing for the opposite nilradical

`ComplexJacquetOneSidedStatement` (module `ComplexJacquetOneSided`) asserts that the vectors
`E^{(0)}_pq v` with `p < q` span a proper subspace `𝔫^{(0)} V` of an irreducible admissible
`(𝔤𝔩_n(ℂ), U(n))`-module `V`. Here `E^{(0)}_pq = ComplexJacquetFinite.ee π 0 p q` is the action
of the matrix unit `E_pq` through the first factor of `𝔤𝔩_n(ℂ) ⊗_ℝ ℂ ≅ 𝔤𝔩_n(ℂ) × 𝔤𝔩_n(ℂ)`.

`ComplexJacquetOneSidedLowerStatement` is the same assertion for the opposite nilradical:
the vectors `E^{(0)}_pq v` with `q < p` span a proper subspace `𝔫⁻^{(0)} V`. The two statements
are equivalent (`complexJacquetOneSided_iff_lower`), so the lower one also implies the Library
target `ComplexJacquetModuleFiniteStatement` (`complexJacquetModuleFinite_of_oneSidedLower`).

Proof idea: the antidiagonal permutation matrix `w₀` is unitary, `w₀² = 1` and
`w₀ E_pq w₀* = E_{p̄ q̄}` with `p̄ = n - 1 - p`. By the conjugation clause of
`IsComplexGKModule`, `ρ(w₀) E^{(0)}_pq = E^{(0)}_{p̄ q̄} ρ(w₀)`, so the bijection `ρ(w₀)` of `V`
exchanges `𝔫^{(0)} V` and `𝔫⁻^{(0)} V`.
-/

noncomputable section

open scoped TensorProduct Matrix

set_option autoImplicit false

namespace Langlands.Archimedean

attribute [local instance 100] LieRing.ofAssociativeRing

namespace ComplexJacquetFinite

open ComplexGenericLarge

section Lower

variable {n : ℕ}

/-- The antidiagonal permutation matrix `w₀`, with `(w₀)_ij = 1` if `j = n - 1 - i`. -/
def revMat (n : ℕ) : Matrix (Fin n) (Fin n) ℂ :=
  Matrix.of fun i j => if Fin.rev i = j then 1 else 0

theorem revMat_apply (i j : Fin n) : revMat n i j = if Fin.rev i = j then 1 else 0 :=
  rfl

theorem revMat_mul_apply (A : Matrix (Fin n) (Fin n) ℂ) (i j : Fin n) :
    (revMat n * A) i j = A (Fin.rev i) j := by
  rw [Matrix.mul_apply, Finset.sum_eq_single (Fin.rev i)]
  · simp [revMat_apply]
  · intro l _ hl
    simp [revMat_apply, Ne.symm hl]
  · simp

theorem mul_star_revMat_apply (A : Matrix (Fin n) (Fin n) ℂ) (i j : Fin n) :
    (A * star (revMat n)) i j = A i (Fin.rev j) := by
  rw [Matrix.mul_apply, Finset.sum_eq_single (Fin.rev j)]
  · simp [revMat_apply, Matrix.star_apply]
  · intro l _ hl
    simp [revMat_apply, Matrix.star_apply, Ne.symm hl]
  · simp

theorem revMat_mul_star : revMat n * star (revMat n) = 1 := by
  ext i j
  rw [mul_star_revMat_apply, revMat_apply, Matrix.one_apply]
  simp only [Fin.rev_inj]

theorem revMat_mul_revMat : revMat n * revMat n = 1 := by
  ext i j
  rw [revMat_mul_apply, revMat_apply, Matrix.one_apply, Fin.rev_rev]

theorem revMat_mul_single_mul (p q : Fin n) :
    revMat n * Matrix.single p q 1 * star (revMat n) =
      Matrix.single (Fin.rev p) (Fin.rev q) 1 := by
  ext i j
  rw [mul_star_revMat_apply, revMat_mul_apply, Matrix.single_apply, Matrix.single_apply]
  congr 1
  apply propext
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨by rw [h1, Fin.rev_rev], by rw [h2, Fin.rev_rev]⟩
  · rintro ⟨h1, h2⟩
    exact ⟨by rw [← h1, Fin.rev_rev], by rw [← h2, Fin.rev_rev]⟩

/-- `w₀` as an element of `U(n)`. -/
def revUnit (n : ℕ) : Matrix.unitaryGroup (Fin n) ℂ :=
  ⟨revMat n, Matrix.mem_unitaryGroup_iff.2 revMat_mul_star⟩

theorem revUnit_mul_self : revUnit n * revUnit n = 1 :=
  Subtype.ext revMat_mul_revMat

variable {V : Type*} [AddCommGroup V] [Module ℂ V]
  (π : (ℂ ⊗[ℝ] Matrix (Fin n) (Fin n) ℂ) →ₗ⁅ℂ⁆ Module.End ℂ V)
  {ρ : Representation ℂ (Matrix.unitaryGroup (Fin n) ℂ) V}

/-- The span of the vectors `E^{(i)}_pq v` with `q < p`, i.e. `𝔫⁻^{(i)} V`. -/
def sideJacquetLower (i : Fin 2) : Submodule ℂ V :=
  Submodule.span ℂ {w | ∃ (p q : Fin n) (v : V), q < p ∧ ee π i p q v = w}

theorem rho_rev_ee (hgk : IsComplexGKModule n ρ π) (p q : Fin n) (v : V) :
    ρ (revUnit n) (ee π 0 p q v) = ee π 0 (Fin.rev p) (Fin.rev q) (ρ (revUnit n) v) := by
  have h := LinearMap.congr_fun
    (rho_mul_pi hgk.2.2.2 (revUnit n) (tensorEquiv.symm (unitPair 0 p q))) v
  simp only [Module.End.mul_apply] at h
  rw [ee, prodAction_apply, h, ee, prodAction_apply]
  congr 2
  rw [← tensorEquiv_symm_pairHom, ← tensorEquiv_symm_pairHom, ← map_mul, ← map_mul]
  congr 1
  funext t
  fin_cases t
  · simp only [Pi.mul_apply, pairHom_zero, Fin.zero_eta, Pi.single_eq_same]
    exact revMat_mul_single_mul p q
  · simp only [Pi.mul_apply, pairHom_one, Fin.mk_one,
      Pi.single_eq_of_ne (show (1 : Fin 2) ≠ 0 by decide), mul_zero, zero_mul]

theorem rho_rev_rev (x : V) : ρ (revUnit n) (ρ (revUnit n) x) = x := by
  rw [← Module.End.mul_apply, ← map_mul, revUnit_mul_self, map_one, Module.End.one_apply]

/-- `ρ(w₀)` maps `𝔫^{(0)} V` into `𝔫⁻^{(0)} V`. -/
theorem rho_rev_mem_lower (hgk : IsComplexGKModule n ρ π) {w : V} (hw : w ∈ sideJacquet π 0) :
    ρ (revUnit n) w ∈ sideJacquetLower π 0 := by
  induction hw using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨p, q, v, hpq, rfl⟩ := hx
    rw [rho_rev_ee π hgk]
    exact Submodule.subset_span ⟨_, _, _, Fin.rev_lt_rev.2 hpq, rfl⟩
  | zero => simp
  | add x y _ _ hx hy => rw [map_add]; exact Submodule.add_mem _ hx hy
  | smul c x _ hx => rw [map_smul]; exact Submodule.smul_mem _ c hx

/-- `ρ(w₀)` maps `𝔫⁻^{(0)} V` into `𝔫^{(0)} V`. -/
theorem rho_rev_mem_upper (hgk : IsComplexGKModule n ρ π) {w : V}
    (hw : w ∈ sideJacquetLower π 0) : ρ (revUnit n) w ∈ sideJacquet π 0 := by
  induction hw using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨p, q, v, hqp, rfl⟩ := hx
    rw [rho_rev_ee π hgk]
    exact ee_mem_sideJacquet π 0 (Fin.rev_lt_rev.2 hqp) _
  | zero => simp
  | add x y _ _ hx hy => rw [map_add]; exact Submodule.add_mem _ hx hy
  | smul c x _ hx => rw [map_smul]; exact Submodule.smul_mem _ c hx

theorem sideJacquet_eq_top_iff_lower (hgk : IsComplexGKModule n ρ π) :
    sideJacquet π 0 = ⊤ ↔ sideJacquetLower π 0 = ⊤ := by
  constructor
  · intro h
    refine eq_top_iff.2 fun x _ => ?_
    rw [← rho_rev_rev (ρ := ρ) x]
    exact rho_rev_mem_lower π hgk (h ▸ Submodule.mem_top)
  · intro h
    refine eq_top_iff.2 fun x _ => ?_
    rw [← rho_rev_rev (ρ := ρ) x]
    exact rho_rev_mem_upper π hgk (h ▸ Submodule.mem_top)

end Lower

end ComplexJacquetFinite

universe uV

/-- **One-sided nonvanishing for the opposite nilradical**: for an irreducible admissible
`(𝔤𝔩_n(ℂ), U(n))`-module, the span of the vectors `E^{(0)}_pq v` with `q < p` is a proper
subspace. -/
def ComplexJacquetOneSidedLowerStatement : Prop :=
  ∀ (n : ℕ) (V : Type uV) [AddCommGroup V] [Module ℂ V]
    (ρ : Representation ℂ (Matrix.unitaryGroup (Fin n) ℂ) V)
    (π : (ℂ ⊗[ℝ] Matrix (Fin n) (Fin n) ℂ) →ₗ⁅ℂ⁆ Module.End ℂ V),
    IsComplexGKModule n ρ π → IsIrreducibleGKModule ρ π → IsAdmissibleGKModule ρ →
      Submodule.span ℂ {w | ∃ (p q : Fin n) (v : V), q < p ∧ ComplexJacquetFinite.ee π 0 p q v = w}
        ≠ ⊤

/-- The lower and upper one-sided statements are equivalent, via `ρ(w₀)`. -/
theorem complexJacquetOneSided_iff_lower :
    ComplexJacquetOneSidedStatement.{uV} ↔ ComplexJacquetOneSidedLowerStatement.{uV} :=
  ⟨fun h n V _ _ ρ π hgk hirr hadm htop => h n V ρ π hgk hirr hadm
      ((ComplexJacquetFinite.sideJacquet_eq_top_iff_lower π hgk).2 htop),
    fun h n V _ _ ρ π hgk hirr hadm htop => h n V ρ π hgk hirr hadm
      ((ComplexJacquetFinite.sideJacquet_eq_top_iff_lower π hgk).1 htop)⟩

/-- The lower one-sided statement implies `ComplexJacquetModuleFiniteStatement`. -/
theorem complexJacquetModuleFinite_of_oneSidedLower :
    ComplexJacquetOneSidedLowerStatement.{uV} → ComplexJacquetModuleFiniteStatement.{uV} :=
  fun h => complexJacquetModuleFinite_of_oneSided (complexJacquetOneSided_iff_lower.2 h)

end Langlands.Archimedean
