import Langlands.Representation.Archimedean.RealPrincipalSeriesQuotientReduction
import Langlands.Representation.Archimedean.ComplexJacquetReduction

/-!
# Jacquet functionals of `(𝔤𝔩_n(ℝ), O(n))`-modules and Casselman's subrepresentation theorem

For a `(𝔤𝔩_n(ℝ), O(n))`-module `(ρ, π)` on `V`, let `𝔫` be the strictly upper triangular real
matrices (the nilradical of the upper triangular Borel subalgebra) and `𝔫V` the span of the
vectors `π(1 ⊗ X) v`, `X ∈ 𝔫`. A *real Jacquet functional* is a linear functional on `V` that
vanishes on `𝔫V`, is an eigenvector of the diagonal directions `E_jj`, and transforms by a sign
under the diagonal sign matrices `s_j = diag(1, …, -1, …, 1)` of `O(n)`:
`ℓ ∘ π(1 ⊗ E_jj) = a_j ℓ` and `ℓ ∘ ρ(s_j) = (-1)^{e_j} ℓ`.

This file states

* `RealJacquetModuleFiniteStatement`: for an irreducible admissible module, `V/𝔫V` is
  finite-dimensional and nonzero (Casselman's theorem in the algebraic setting; Wallach 1979,
  4.13–4.16);
* `RealJacquetFrobeniusStatement`: a nonzero real Jacquet functional gives a nonzero
  intertwining map into the `O(n)`-finite principal series of the `n` real characters cut out
  by its exponents and signs (Frobenius reciprocity; Wallach 1979, 4.16–4.17);

and proves that the two imply `RealPrincipalSeriesSubrepresentationStatement`
(`realPrincipalSeriesSubrepresentationJacquetReduction`).
-/

noncomputable section

open scoped TensorProduct Matrix

set_option autoImplicit false

namespace Langlands.Archimedean

attribute [local instance 100] LieRing.ofAssociativeRing

open Langlands.LocalFactor.Archimedean

universe uV

section Jacquet

variable (n : ℕ) {V : Type uV} [AddCommGroup V] [Module ℂ V]

/-- The subspace `𝔫V` of a `(𝔤𝔩_n(ℝ), O(n))`-module: the span of the vectors `π(1 ⊗ X) v`
for strictly upper triangular real matrices `X` (`X i j = 0` for `j ≤ i`). The quotient
`V/𝔫V` is the Jacquet module of `V` along the upper triangular Borel subalgebra. -/
def realJacquetSubspace (π : (ℂ ⊗[ℝ] Matrix (Fin n) (Fin n) ℝ) →ₗ⁅ℂ⁆ Module.End ℂ V) :
    Submodule ℂ V :=
  Submodule.span ℂ {w | ∃ (X : Matrix (Fin n) (Fin n) ℝ) (v : V),
    (∀ i j : Fin n, (j : ℕ) ≤ i → X i j = 0) ∧ π (1 ⊗ₜ X) v = w}

/-- The diagonal sign matrix `s_j` with `-1` at position `j` and `1` at every other position,
as an element of `O(n)`. -/
def signReflection (j : Fin n) : Matrix.unitaryGroup (Fin n) ℝ :=
  ⟨Matrix.diagonal fun i => if i = j then -1 else 1, by
    rw [Matrix.mem_unitaryGroup_iff, Matrix.star_eq_conjTranspose, Matrix.diagonal_conjTranspose,
      Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
    congr 1
    funext i
    by_cases h : i = j <;> simp [h]⟩

/-- `ℓ` is a real Jacquet functional with exponents `a` and signs `e`: it vanishes on
`π(1 ⊗ X) V` for every strictly upper triangular real matrix `X`, and for every position `j`
it is an eigenvector of the diagonal direction `E_jj` with eigenvalue `a j` and of the sign
matrix `s_j` with eigenvalue `(-1)^{e j}`: `ℓ(π(1 ⊗ E_jj) v) = a_j ℓ(v)` and
`ℓ(ρ(s_j) v) = (-1)^{e_j} ℓ(v)`. -/
def IsRealJacquetFunctional (ρ : Representation ℂ (Matrix.unitaryGroup (Fin n) ℝ) V)
    (π : (ℂ ⊗[ℝ] Matrix (Fin n) (Fin n) ℝ) →ₗ⁅ℂ⁆ Module.End ℂ V)
    (ℓ : V →ₗ[ℂ] ℂ) (a : Fin n → ℂ) (e : Fin n → Fin 2) : Prop :=
  (∀ X : Matrix (Fin n) (Fin n) ℝ, (∀ i j : Fin n, (j : ℕ) ≤ i → X i j = 0) →
    ∀ v : V, ℓ (π (1 ⊗ₜ X) v) = 0) ∧
  ∀ (j : Fin n) (v : V),
    ℓ (π (1 ⊗ₜ Matrix.single j j 1) v) = a j * ℓ v ∧
      ℓ (ρ (signReflection n j) v) = (-1) ^ (e j).val * ℓ v

end Jacquet

/-- Casselman's theorem for `(𝔤𝔩_n(ℝ), O(n))`-modules, algebraic form (Wallach 1979, 4.13–4.16,
for the upper triangular Borel subalgebra): for an irreducible admissible module the Jacquet
module `V/𝔫V` is finite-dimensional and nonzero. -/
def RealJacquetModuleFiniteStatement : Prop :=
  ∀ (n : ℕ) (V : Type uV) [AddCommGroup V] [Module ℂ V]
    (ρ : Representation ℂ (Matrix.unitaryGroup (Fin n) ℝ) V)
    (π : (ℂ ⊗[ℝ] Matrix (Fin n) (Fin n) ℝ) →ₗ⁅ℂ⁆ Module.End ℂ V),
    IsRealGKModule n ρ π → IsIrreducibleGKModule ρ π → IsAdmissibleGKModule ρ →
      FiniteDimensional ℂ (V ⧸ realJacquetSubspace n π) ∧ realJacquetSubspace n π ≠ ⊤

/-- Frobenius reciprocity for real Jacquet functionals (Wallach 1979, 4.16–4.17, for `GL_n(ℝ)`
and its upper triangular Borel subgroup). Let `(ρ, π)` be a `(𝔤𝔩_n(ℝ), O(n))`-module and `ℓ` a
nonzero real Jacquet functional with exponents `a` and signs `e`. Then there are `n` real
characters `c 0, …, c (n-1)`, `c_j(x) = sgn(x)^{e_j} |x|^{t_j}`, with parity `e_j` and
exponent `t_j = a_j - (n - 1)/2 + j`, and a nonzero intertwining map `B` from `V` into the
`O(n)`-finite functions of the principal series of these characters, in this order. -/
def RealJacquetFrobeniusStatement : Prop :=
  ∀ (n : ℕ) (V : Type uV) [AddCommGroup V] [Module ℂ V]
    (ρ : Representation ℂ (Matrix.unitaryGroup (Fin n) ℝ) V)
    (π : (ℂ ⊗[ℝ] Matrix (Fin n) (Fin n) ℝ) →ₗ⁅ℂ⁆ Module.End ℂ V),
    IsRealGKModule n ρ π →
      ∀ (ℓ : V →ₗ[ℂ] ℂ) (a : Fin n → ℂ) (e : Fin n → Fin 2), ℓ ≠ 0 →
        IsRealJacquetFunctional n ρ π ℓ a e →
        ∃ c : Fin n → RealCharacterData,
          (∀ j : Fin n, (c j).parity = e j) ∧
          (∀ j : Fin n, (c j).exponent + ((n : ℂ) - 1) / 2 - ((j : ℕ) : ℂ) = a j) ∧
          ∃ B : V →ₗ[ℂ] kFiniteFunctions
              (realStandardModule n ((List.ofFn c).map RealBlock.character))
              (unitaryCompact ℝ n),
            B ≠ 0 ∧ IsRealStandardEmbedding n ρ π ((List.ofFn c).map RealBlock.character) B

/-- Casselman's algebraic theorem and Frobenius reciprocity give Casselman's subrepresentation
theorem for `GL_n(ℝ)`. -/
def RealPrincipalSeriesSubrepresentationJacquetReductionStatement : Prop :=
  RealJacquetModuleFiniteStatement.{uV} → RealJacquetFrobeniusStatement.{uV} →
    RealPrincipalSeriesSubrepresentationStatement.{uV}

/-! ## The operators on the Jacquet module -/

section Reduction

variable {n : ℕ} {V : Type uV} [AddCommGroup V] [Module ℂ V]
  {ρ : Representation ℂ (Matrix.unitaryGroup (Fin n) ℝ) V}
  {π : (ℂ ⊗[ℝ] Matrix (Fin n) (Fin n) ℝ) →ₗ⁅ℂ⁆ Module.End ℂ V}

/-- `π(1 ⊗ [D, X]) = [π(1 ⊗ D), π(1 ⊗ X)]`. -/
theorem real_map_commutator (π : (ℂ ⊗[ℝ] Matrix (Fin n) (Fin n) ℝ) →ₗ⁅ℂ⁆ Module.End ℂ V)
    (D X : Matrix (Fin n) (Fin n) ℝ) :
    π (1 ⊗ₜ (D * X - X * D)) = π (1 ⊗ₜ D) * π (1 ⊗ₜ X) - π (1 ⊗ₜ X) * π (1 ⊗ₜ D) := by
  calc π (1 ⊗ₜ (D * X - X * D))
      = π ⁅(1 : ℂ) ⊗ₜ[ℝ] D, (1 : ℂ) ⊗ₜ[ℝ] X⁆ := by
        rw [LieAlgebra.ExtendScalars.bracket_tmul, mul_one, Ring.lie_def]
    _ = ⁅π (1 ⊗ₜ D), π (1 ⊗ₜ X)⁆ := LieHom.map_lie π _ _
    _ = _ := Ring.lie_def _ _

theorem real_single_mul_strict_sub_mem (j : Fin n) (X : Matrix (Fin n) (Fin n) ℝ)
    (hX : ∀ i k : Fin n, (k : ℕ) ≤ i → X i k = 0) :
    ∀ i k : Fin n, (k : ℕ) ≤ i →
      (Matrix.single j j (1 : ℝ) * X - X * Matrix.single j j 1 : Matrix (Fin n) (Fin n) ℝ) i k =
        0 := by
  intro i k hik
  have h1 : (Matrix.single j j (1 : ℝ) * X) i k = 0 := by
    by_cases hij : i = j
    · subst hij
      rw [Matrix.single_mul_apply_same, hX i k hik, mul_zero]
    · exact Matrix.single_mul_apply_of_ne 1 j j i k hij X
  have h2 : (X * Matrix.single j j (1 : ℝ)) i k = 0 := by
    by_cases hkj : k = j
    · subst hkj
      rw [Matrix.mul_single_apply_same, hX i k hik, zero_mul]
    · exact Matrix.mul_single_apply_of_ne 1 j j i k hkj X
  rw [Matrix.sub_apply, h1, h2, sub_zero]

theorem signReflection_val (j : Fin n) :
    ((signReflection n j : Matrix.unitaryGroup (Fin n) ℝ) : Matrix (Fin n) (Fin n) ℝ) =
      Matrix.diagonal fun i => if i = j then -1 else 1 := rfl

theorem star_signReflection_val (j : Fin n) :
    (star (signReflection n j : Matrix (Fin n) (Fin n) ℝ)) =
      Matrix.diagonal fun i => if i = j then -1 else 1 := by
  rw [signReflection_val, Matrix.star_eq_conjTranspose, Matrix.diagonal_conjTranspose]
  congr 1

/-- Conjugation by a sign matrix multiplies the entry `(i, k)` by the signs at `i` and `k`. -/
theorem signReflection_conj_apply (j : Fin n) (X : Matrix (Fin n) (Fin n) ℝ) (i k : Fin n) :
    ((signReflection n j : Matrix (Fin n) (Fin n) ℝ) * X *
        star (signReflection n j : Matrix (Fin n) (Fin n) ℝ)) i k =
      (if i = j then -1 else 1) * X i k * (if k = j then -1 else 1) := by
  rw [star_signReflection_val, signReflection_val, Matrix.mul_diagonal, Matrix.diagonal_mul]

theorem signReflection_conj_single (j l : Fin n) :
    (signReflection n j : Matrix (Fin n) (Fin n) ℝ) * Matrix.single l l 1 *
        star (signReflection n j : Matrix (Fin n) (Fin n) ℝ) = Matrix.single l l 1 := by
  ext i k
  rw [signReflection_conj_apply, Matrix.single_apply]
  by_cases hi : l = i
  · by_cases hk : l = k
    · subst hi hk
      by_cases h : l = j <;> simp [h]
    · have hik : i ≠ k := fun h => hk (hi.trans h)
      simp [hi, hik]
  · simp [hi]

theorem signReflection_mul_comm (i j : Fin n) :
    signReflection n i * signReflection n j = signReflection n j * signReflection n i := by
  apply Subtype.ext
  change Matrix.diagonal _ * Matrix.diagonal _ = Matrix.diagonal _ * Matrix.diagonal _
  rw [Matrix.diagonal_mul_diagonal, Matrix.diagonal_mul_diagonal]
  congr 1
  funext k
  ring

theorem signReflection_mul_self (j : Fin n) : signReflection n j * signReflection n j = 1 := by
  apply Subtype.ext
  change Matrix.diagonal _ * Matrix.diagonal _ = (1 : Matrix (Fin n) (Fin n) ℝ)
  rw [Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
  congr 1
  funext k
  by_cases h : k = j <;> simp [h]

/-- The operators used on the Jacquet module: `π(1 ⊗ E_jj)` (left summand) and the sign
matrices `ρ(s_j)` (right summand). -/
def jacquetOp (ρ : Representation ℂ (Matrix.unitaryGroup (Fin n) ℝ) V)
    (π : (ℂ ⊗[ℝ] Matrix (Fin n) (Fin n) ℝ) →ₗ⁅ℂ⁆ Module.End ℂ V) :
    Fin n ⊕ Fin n → Module.End ℂ V
  | Sum.inl j => π (1 ⊗ₜ Matrix.single j j 1)
  | Sum.inr j => ρ (signReflection n j)

theorem mem_realJacquetSubspace {X : Matrix (Fin n) (Fin n) ℝ}
    (hX : ∀ i j : Fin n, (j : ℕ) ≤ i → X i j = 0) (v : V) :
    π (1 ⊗ₜ X) v ∈ realJacquetSubspace n π :=
  Submodule.subset_span ⟨X, v, hX, rfl⟩

theorem jacquetOp_mem (hgk : IsRealGKModule n ρ π) (p : Fin n ⊕ Fin n) :
    ∀ w ∈ realJacquetSubspace n π, jacquetOp ρ π p w ∈ realJacquetSubspace n π := by
  intro w hw
  induction hw using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨X, v, hX, rfl⟩ := hx
    cases p with
    | inl j =>
      have h := congrArg (fun f : Module.End ℂ V => f v) (real_map_commutator π
        (Matrix.single j j 1) X)
      simp only [LinearMap.sub_apply, Module.End.mul_apply] at h
      have h' : π (1 ⊗ₜ Matrix.single j j 1) (π (1 ⊗ₜ X) v) =
          π (1 ⊗ₜ (Matrix.single j j 1 * X - X * Matrix.single j j 1)) v +
            π (1 ⊗ₜ X) (π (1 ⊗ₜ Matrix.single j j 1) v) := by
        rw [h]; abel
      change π (1 ⊗ₜ Matrix.single j j 1) (π (1 ⊗ₜ X) v) ∈ _
      rw [h']
      exact Submodule.add_mem _
        (mem_realJacquetSubspace (real_single_mul_strict_sub_mem j X hX) v)
        (mem_realJacquetSubspace hX _)
    | inr j =>
      change ρ (signReflection n j) (π (1 ⊗ₜ X) v) ∈ _
      rw [hgk.2.2.2 (signReflection n j) X v]
      refine mem_realJacquetSubspace (fun i k hik => ?_) _
      rw [signReflection_conj_apply, hX i k hik, mul_zero, zero_mul]
  | zero => simp
  | add x y _ _ hx hy => rw [map_add]; exact Submodule.add_mem _ hx hy
  | smul r x _ hx => rw [map_smul]; exact Submodule.smul_mem _ r hx

theorem jacquetOp_commute (hgk : IsRealGKModule n ρ π) (p q : Fin n ⊕ Fin n) :
    Commute (jacquetOp ρ π p) (jacquetOp ρ π q) := by
  -- Diagonal directions commute with each other and with the sign matrices.
  have hdd : ∀ i j : Fin n, Commute (π (1 ⊗ₜ Matrix.single i i (1 : ℝ)))
      (π (1 ⊗ₜ Matrix.single j j (1 : ℝ))) := by
    intro i j
    have hc : Matrix.single i i (1 : ℝ) * Matrix.single j j 1 -
        Matrix.single j j 1 * Matrix.single i i 1 = 0 := by
      by_cases h : i = j
      · subst h; rw [sub_self]
      · rw [Matrix.single_mul_single_of_ne _ _ _ _ h,
          Matrix.single_mul_single_of_ne _ _ _ _ (Ne.symm h), sub_self]
    have h := real_map_commutator π (Matrix.single i i 1) (Matrix.single j j 1)
    rw [hc, TensorProduct.tmul_zero, map_zero] at h
    exact (sub_eq_zero.mp h.symm)
  have hsd : ∀ i j : Fin n, Commute (ρ (signReflection n i))
      (π (1 ⊗ₜ Matrix.single j j (1 : ℝ))) := by
    intro i j
    apply LinearMap.ext
    intro v
    change ρ (signReflection n i) (π (1 ⊗ₜ Matrix.single j j 1) v) =
      π (1 ⊗ₜ Matrix.single j j 1) (ρ (signReflection n i) v)
    rw [hgk.2.2.2, signReflection_conj_single]
  have hss : ∀ i j : Fin n, Commute (ρ (signReflection n i)) (ρ (signReflection n j)) := by
    intro i j
    change ρ (signReflection n i) * ρ (signReflection n j) =
      ρ (signReflection n j) * ρ (signReflection n i)
    rw [← map_mul, ← map_mul, signReflection_mul_comm]
  cases p with
  | inl i => cases q with
    | inl j => exact hdd i j
    | inr j => exact (hsd j i).symm
  | inr i => cases q with
    | inl j => exact hsd i j
    | inr j => exact hss i j

/-- The operators on the Jacquet module `V/𝔫V`. -/
def jacquetQuotOp (hgk : IsRealGKModule n ρ π) (p : Fin n ⊕ Fin n) :
    Module.End ℂ (V ⧸ realJacquetSubspace n π) :=
  (realJacquetSubspace n π).mapQ (realJacquetSubspace n π) (jacquetOp ρ π p)
    (fun w hw => jacquetOp_mem hgk p w hw)

theorem jacquetQuotOp_mkQ (hgk : IsRealGKModule n ρ π) (p : Fin n ⊕ Fin n) (v : V) :
    jacquetQuotOp hgk p ((realJacquetSubspace n π).mkQ v) =
      (realJacquetSubspace n π).mkQ (jacquetOp ρ π p v) := rfl

theorem jacquetQuotOp_commute (hgk : IsRealGKModule n ρ π) (p q : Fin n ⊕ Fin n) :
    Commute (jacquetQuotOp hgk p) (jacquetQuotOp hgk q) := by
  apply Submodule.linearMap_qext
  apply LinearMap.ext
  intro v
  change jacquetQuotOp hgk p (jacquetQuotOp hgk q ((realJacquetSubspace n π).mkQ v)) =
    jacquetQuotOp hgk q (jacquetQuotOp hgk p ((realJacquetSubspace n π).mkQ v))
  rw [jacquetQuotOp_mkQ, jacquetQuotOp_mkQ, jacquetQuotOp_mkQ, jacquetQuotOp_mkQ]
  exact congrArg _ (LinearMap.congr_fun (jacquetOp_commute hgk p q).eq v)

/-- The transposed operators on the dual of the Jacquet module. -/
def jacquetQuotDualOp (hgk : IsRealGKModule n ρ π) (p : Fin n ⊕ Fin n) :
    Module.End ℂ (Module.Dual ℂ (V ⧸ realJacquetSubspace n π)) :=
  (jacquetQuotOp hgk p).dualMap

theorem jacquetQuotDualOp_commute (hgk : IsRealGKModule n ρ π) (p q : Fin n ⊕ Fin n) :
    Commute (jacquetQuotDualOp hgk p) (jacquetQuotDualOp hgk q) := by
  change (jacquetQuotOp hgk p).dualMap ∘ₗ (jacquetQuotOp hgk q).dualMap =
    (jacquetQuotOp hgk q).dualMap ∘ₗ (jacquetQuotOp hgk p).dualMap
  rw [LinearMap.dualMap_comp_dualMap, LinearMap.dualMap_comp_dualMap]
  exact congrArg LinearMap.dualMap (jacquetQuotOp_commute hgk q p).eq

/-- A complex number whose square is `1` is `(-1)^e` for some `e : Fin 2`. -/
theorem exists_fin_two_of_sq_eq_one {c : ℂ} (hc : c ^ 2 = 1) :
    ∃ e : Fin 2, c = (-1) ^ e.val := by
  rcases sq_eq_one_iff.mp hc with h | h
  · exact ⟨0, by simpa using h⟩
  · exact ⟨1, by simpa using h⟩

/-- A nonzero finite-dimensional Jacquet module carries a nonzero real Jacquet functional. -/
theorem exists_isRealJacquetFunctional (hgk : IsRealGKModule n ρ π)
    (hfin : FiniteDimensional ℂ (V ⧸ realJacquetSubspace n π))
    (hne : realJacquetSubspace n π ≠ ⊤) :
    ∃ (ℓ : V →ₗ[ℂ] ℂ) (a : Fin n → ℂ) (e : Fin n → Fin 2), ℓ ≠ 0 ∧
      IsRealJacquetFunctional n ρ π ℓ a e := by
  classical
  have := hfin
  have : Nontrivial (V ⧸ realJacquetSubspace n π) :=
    Submodule.Quotient.nontrivial_iff.mpr hne
  obtain ⟨x, hx⟩ := exists_ne (0 : Module.Dual ℂ (V ⧸ realJacquetSubspace n π))
  obtain ⟨w, -, hw0, hw⟩ := exists_common_eigenvector_of_commute (jacquetQuotDualOp hgk)
    (jacquetQuotDualOp_commute hgk) Finset.univ ⊤ inferInstance
    ((Submodule.ne_bot_iff _).mpr ⟨x, trivial, hx⟩) (fun _ _ _ => trivial)
  choose c hc using fun p => hw p (Finset.mem_univ p)
  obtain ⟨ℓ, hℓdef⟩ : ∃ ℓ : V →ₗ[ℂ] ℂ, ℓ = w ∘ₗ (realJacquetSubspace n π).mkQ := ⟨_, rfl⟩
  have key : ∀ p v, ℓ (jacquetOp ρ π p v) = c p * ℓ v := by
    intro p v
    have h := LinearMap.congr_fun (hc p) ((realJacquetSubspace n π).mkQ v)
    rw [jacquetQuotDualOp, LinearMap.dualMap_apply, jacquetQuotOp_mkQ] at h
    rw [hℓdef, LinearMap.comp_apply, LinearMap.comp_apply, h, LinearMap.smul_apply, smul_eq_mul]
  have hℓ0 : ℓ ≠ 0 := by
    intro h
    apply hw0
    apply Submodule.linearMap_qext
    rw [← hℓdef, h, LinearMap.zero_comp]
  -- The sign eigenvalues square to one.
  have hsq : ∀ j : Fin n, c (Sum.inr j) ^ 2 = 1 := by
    intro j
    obtain ⟨v, hv⟩ : ∃ v, ℓ v ≠ 0 := by
      by_contra h
      exact hℓ0 (LinearMap.ext fun v => not_not.mp fun hv => h ⟨v, hv⟩)
    have h1 := key (Sum.inr j) (jacquetOp ρ π (Sum.inr j) v)
    rw [key (Sum.inr j) v] at h1
    have h2 : jacquetOp ρ π (Sum.inr j) (jacquetOp ρ π (Sum.inr j) v) = v := by
      change ρ (signReflection n j) (ρ (signReflection n j) v) = v
      rw [← Module.End.mul_apply, ← map_mul, signReflection_mul_self, map_one,
        Module.End.one_apply]
    rw [h2] at h1
    have h3 : (c (Sum.inr j) ^ 2 - 1) * ℓ v = 0 := by
      linear_combination -h1
    rcases mul_eq_zero.mp h3 with h | h
    · exact sub_eq_zero.mp h
    · exact absurd h hv
  choose e he using fun j => exists_fin_two_of_sq_eq_one (hsq j)
  refine ⟨ℓ, fun j => c (Sum.inl j), e, hℓ0, fun X hX v => ?_, fun j v => ⟨?_, ?_⟩⟩
  · rw [hℓdef, LinearMap.comp_apply, Submodule.mkQ_apply,
      (Submodule.Quotient.mk_eq_zero _).mpr (mem_realJacquetSubspace hX v), map_zero]
  · exact key (Sum.inl j) v
  · rw [← he j]
    exact key (Sum.inr j) v

end Reduction

/-- Proof of the reduction. By Casselman's theorem `V/𝔫V` is finite-dimensional and nonzero.
The diagonal directions `π(1 ⊗ E_jj)` and the sign matrices `ρ(s_j)` preserve `𝔫V` and commute,
so their transposes on the dual of `V/𝔫V` have a common eigenvector. Pulled back to `V` it is a
nonzero real Jacquet functional; the eigenvalue of each `ρ(s_j)` is a sign because
`s_j² = 1`. Frobenius reciprocity turns it into the required embedding. -/
theorem realPrincipalSeriesSubrepresentationJacquetReduction :
    RealPrincipalSeriesSubrepresentationJacquetReductionStatement.{uV} := by
  intro hA hF n V _ _ ρ π hgk hirr hadm
  obtain ⟨hfin, hne⟩ := hA n V ρ π hgk hirr hadm
  obtain ⟨ℓ, a, e, hℓ0, hℓ⟩ := exists_isRealJacquetFunctional hgk hfin hne
  obtain ⟨c, -, -, B, hB0, hB⟩ := hF n V ρ π hgk ℓ a e hℓ0 hℓ
  exact ⟨List.ofFn c, List.length_ofFn, B, hB0, hB⟩

end Langlands.Archimedean
