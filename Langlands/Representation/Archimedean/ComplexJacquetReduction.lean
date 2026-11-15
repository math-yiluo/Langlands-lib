import Langlands.Representation.Archimedean.GKModule
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.LinearAlgebra.Eigenspace.Minpoly
import Mathlib.LinearAlgebra.Eigenspace.Triangularizable
import Mathlib.Analysis.Complex.Polynomial.Basic

/-!
# Jacquet functionals of `(𝔤𝔩_n(ℂ), U(n))`-modules and the ordering of their exponents

For a `(𝔤𝔩_n(ℂ), U(n))`-module `(ρ, π)` on `V`, let `𝔫` be the strictly upper triangular
complex matrices (the nilradical of the upper triangular Borel subalgebra) and `𝔫V` the span of
the vectors `π(1 ⊗ X) v`, `X ∈ 𝔫`. A *Jacquet functional* is a linear functional on `V` that
vanishes on `𝔫V` and is an eigenvector for the diagonal Cartan subalgebra: for every position
`j`, `ℓ ∘ π(1 ⊗ E_jj) = a_j ℓ` and `ℓ ∘ π(1 ⊗ i E_jj) = b_j ℓ`.

This file states

* `ComplexJacquetModuleFiniteStatement`: for an irreducible admissible module, `V/𝔫V` is
  finite-dimensional and nonzero (Casselman's theorem in the algebraic setting; Wallach 1979,
  4.13–4.14);
* `ComplexJacquetRankOneStatement`: a rank-one reordering step for the exponents of Jacquet
  functionals;
* `ComplexOrderedJacquetFunctionalStatement`: an irreducible admissible module has a nonzero
  Jacquet functional whose exponents are ordered, `Re a_i + 2i ≤ Re a_j + 2j` for `i < j`;

and proves that the first two imply the third (`complexOrderedJacquetReduction`).
-/

noncomputable section

open scoped TensorProduct Matrix

set_option autoImplicit false

namespace Langlands.Archimedean

attribute [local instance 100] LieRing.ofAssociativeRing

universe uV

section Jacquet

variable (n : ℕ) {V : Type uV} [AddCommGroup V] [Module ℂ V]

/-- The subspace `𝔫V` of a `(𝔤𝔩_n(ℂ), U(n))`-module: the span of the vectors `π(1 ⊗ X) v`
for strictly upper triangular complex matrices `X` (`X i j = 0` for `j ≤ i`). The quotient
`V/𝔫V` is the Jacquet module of `V` along the upper triangular Borel subalgebra. -/
def complexJacquetSubspace (π : (ℂ ⊗[ℝ] Matrix (Fin n) (Fin n) ℂ) →ₗ⁅ℂ⁆ Module.End ℂ V) :
    Submodule ℂ V :=
  Submodule.span ℂ {w | ∃ (X : Matrix (Fin n) (Fin n) ℂ) (v : V),
    (∀ i j : Fin n, (j : ℕ) ≤ i → X i j = 0) ∧ π (1 ⊗ₜ X) v = w}

/-- `ℓ` is a Jacquet functional with exponents `a`, `b`: it vanishes on `π(1 ⊗ X) V` for every
strictly upper triangular complex matrix `X`, and for every position `j` it is an eigenvector of
the real diagonal direction `E_jj` with eigenvalue `a j` and of the imaginary diagonal direction
`i E_jj` with eigenvalue `b j`: `ℓ(π(1 ⊗ E_jj) v) = a_j ℓ(v)` and
`ℓ(π(1 ⊗ i E_jj) v) = b_j ℓ(v)`. -/
def IsComplexJacquetFunctional
    (π : (ℂ ⊗[ℝ] Matrix (Fin n) (Fin n) ℂ) →ₗ⁅ℂ⁆ Module.End ℂ V)
    (ℓ : V →ₗ[ℂ] ℂ) (a b : Fin n → ℂ) : Prop :=
  (∀ X : Matrix (Fin n) (Fin n) ℂ, (∀ i j : Fin n, (j : ℕ) ≤ i → X i j = 0) →
    ∀ v : V, ℓ (π (1 ⊗ₜ X) v) = 0) ∧
  ∀ (j : Fin n) (v : V),
    ℓ (π (1 ⊗ₜ Matrix.single j j 1) v) = a j * ℓ v ∧
      ℓ (π (1 ⊗ₜ Matrix.single j j Complex.I) v) = b j * ℓ v

end Jacquet

/-- Casselman's theorem for `(𝔤𝔩_n(ℂ), U(n))`-modules, algebraic form (Wallach 1979, 4.13 and
4.14, for the upper triangular Borel subalgebra): for an irreducible admissible module the
Jacquet module `V/𝔫V` is finite-dimensional and nonzero. -/
def ComplexJacquetModuleFiniteStatement : Prop :=
  ∀ (n : ℕ) (V : Type uV) [AddCommGroup V] [Module ℂ V]
    (ρ : Representation ℂ (Matrix.unitaryGroup (Fin n) ℂ) V)
    (π : (ℂ ⊗[ℝ] Matrix (Fin n) (Fin n) ℂ) →ₗ⁅ℂ⁆ Module.End ℂ V),
    IsComplexGKModule n ρ π → IsIrreducibleGKModule ρ π → IsAdmissibleGKModule ρ →
      FiniteDimensional ℂ (V ⧸ complexJacquetSubspace n π) ∧
        complexJacquetSubspace n π ≠ ⊤

/-- Rank-one reordering of Jacquet exponents. Let `ℓ` be a nonzero Jacquet functional of an
irreducible admissible module with exponents `a`, `b`, and let `j = i + 1` be adjacent positions
with `Re a_j + 2 < Re a_i`. Then there is a nonzero Jacquet functional `ℓ'` with exponents
`a'`, `b'` that agrees with `a` off `{i, j}`, has the same sum `a'_i + a'_j = a_i + a_j`, and is
ordered at `(i, j)`: `Re a'_i ≤ Re a'_j + 2`. (With `a_j = 2t_j + (n - 1) - 2j`, the conditions
say `Re t_i > Re t_j` and `Re t'_i ≤ Re t'_j`.) -/
def ComplexJacquetRankOneStatement : Prop :=
  ∀ (n : ℕ) (V : Type uV) [AddCommGroup V] [Module ℂ V]
    (ρ : Representation ℂ (Matrix.unitaryGroup (Fin n) ℂ) V)
    (π : (ℂ ⊗[ℝ] Matrix (Fin n) (Fin n) ℂ) →ₗ⁅ℂ⁆ Module.End ℂ V),
    IsComplexGKModule n ρ π → IsIrreducibleGKModule ρ π → IsAdmissibleGKModule ρ →
      ∀ (ℓ : V →ₗ[ℂ] ℂ) (a b : Fin n → ℂ), ℓ ≠ 0 → IsComplexJacquetFunctional n π ℓ a b →
        ∀ i j : Fin n, (j : ℕ) = i + 1 → (a j).re + 2 < (a i).re →
          ∃ (ℓ' : V →ₗ[ℂ] ℂ) (a' b' : Fin n → ℂ), ℓ' ≠ 0 ∧
            IsComplexJacquetFunctional n π ℓ' a' b' ∧
            (∀ k : Fin n, k ≠ i → k ≠ j → a' k = a k) ∧ a' i + a' j = a i + a j ∧
            (a' i).re ≤ (a' j).re + 2

/-- Ordered Jacquet functionals: every irreducible admissible `(𝔤𝔩_n(ℂ), U(n))`-module has a
nonzero Jacquet functional whose real exponents `a` satisfy `Re a_i + 2i ≤ Re a_j + 2j` for
`i < j`, that is, `Re t_i ≤ Re t_j` for `a_j = 2t_j + (n - 1) - 2j`. -/
def ComplexOrderedJacquetFunctionalStatement : Prop :=
  ∀ (n : ℕ) (V : Type uV) [AddCommGroup V] [Module ℂ V]
    (ρ : Representation ℂ (Matrix.unitaryGroup (Fin n) ℂ) V)
    (π : (ℂ ⊗[ℝ] Matrix (Fin n) (Fin n) ℂ) →ₗ⁅ℂ⁆ Module.End ℂ V),
    IsComplexGKModule n ρ π → IsIrreducibleGKModule ρ π → IsAdmissibleGKModule ρ →
      ∃ (ℓ : V →ₗ[ℂ] ℂ) (a b : Fin n → ℂ), ℓ ≠ 0 ∧ IsComplexJacquetFunctional n π ℓ a b ∧
        ∀ i j : Fin n, i < j → (a i).re + 2 * ((i : ℕ) : ℝ) ≤ (a j).re + 2 * ((j : ℕ) : ℝ)

/-- Casselman's theorem and the rank-one step give ordered Jacquet functionals. -/
def ComplexOrderedJacquetReductionStatement : Prop :=
  ComplexJacquetModuleFiniteStatement.{uV} → ComplexJacquetRankOneStatement.{uV} →
    ComplexOrderedJacquetFunctionalStatement.{uV}

/-! ## Common eigenvectors -/

section Eigen

variable {W : Type*} [AddCommGroup W] [Module ℂ W]

/-- A finite family of pairwise commuting endomorphisms has a common eigenvector in every
nonzero finite-dimensional subspace stable under all of them. -/
theorem exists_common_eigenvector_of_commute {ι : Type*} (T : ι → Module.End ℂ W)
    (hT : ∀ i j, Commute (T i) (T j)) (s : Finset ι) :
    ∀ U : Submodule ℂ W, FiniteDimensional ℂ U → U ≠ ⊥ → (∀ i, ∀ w ∈ U, T i w ∈ U) →
      ∃ w ∈ U, w ≠ 0 ∧ ∀ i ∈ s, ∃ c : ℂ, T i w = c • w := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    intro U _ hU _
    obtain ⟨w, hw, hw0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hU
    exact ⟨w, hw, hw0, by simp⟩
  | insert i s _ ih =>
    intro U hUf hU hUT
    have : Nontrivial U := Submodule.nontrivial_iff_ne_bot.mpr hU
    obtain ⟨c, hc⟩ := Module.End.exists_eigenvalue ((T i).restrict (hUT i))
    obtain ⟨x, hx⟩ := hc.exists_hasEigenvector
    set E : Submodule ℂ W := U ⊓ Module.End.eigenspace (T i) c with hE
    have hxE : (x : W) ∈ E := by
      refine ⟨x.2, ?_⟩
      rw [SetLike.mem_coe, Module.End.mem_eigenspace_iff]
      have := congrArg Subtype.val hx.apply_eq_smul
      simpa using this
    have hx0 : (x : W) ≠ 0 := fun h => hx.2 (Subtype.ext h)
    have hEf : FiniteDimensional ℂ E := Submodule.finiteDimensional_of_le inf_le_left
    have hE0 : E ≠ ⊥ := fun h => hx0 (by rw [h] at hxE; exact hxE)
    have hET : ∀ j, ∀ w ∈ E, T j w ∈ E := by
      intro j w hw
      refine ⟨hUT j w hw.1, ?_⟩
      have hw2 : T i w = c • w := Module.End.mem_eigenspace_iff.mp hw.2
      rw [SetLike.mem_coe, Module.End.mem_eigenspace_iff]
      have h := congrArg (fun f : Module.End ℂ W => f w) (hT i j).eq
      simp only [Module.End.mul_apply] at h
      rw [h, hw2, map_smul]
    obtain ⟨w, hwE, hw0, hws⟩ := ih E hEf hE0 hET
    refine ⟨w, hwE.1, hw0, ?_⟩
    intro j hj
    rcases Finset.mem_insert.mp hj with rfl | hj
    · exact ⟨c, Module.End.mem_eigenspace_iff.mp hwE.2⟩
    · exact hws j hj

end Eigen

/-! ## Monotonicity from adjacent steps -/

/-- A function on `Fin n` that does not decrease along adjacent positions is monotone. -/
theorem fin_le_of_adjacent_le {n : ℕ} (g : Fin n → ℝ)
    (h : ∀ i j : Fin n, (j : ℕ) = i + 1 → g i ≤ g j) :
    ∀ i j : Fin n, i < j → g i ≤ g j := by
  intro i j hij
  have key : ∀ d : ℕ, ∀ k : Fin n, (k : ℕ) = i + d → g i ≤ g k := by
    intro d
    induction d with
    | zero =>
      intro k hk
      rw [show k = i from Fin.ext (by simpa using hk)]
    | succ d ih =>
      intro k hk
      have hlt : (i : ℕ) + d < n := by have := k.2; omega
      exact (ih ⟨i + d, hlt⟩ rfl).trans (h _ k (by simp only; omega))
  exact key ((j : ℕ) - i) j (by have : (i : ℕ) < j := hij; omega)

/-! ## The reduction -/

section Reduction

variable {n : ℕ} {V : Type uV} [AddCommGroup V] [Module ℂ V]
  (π : (ℂ ⊗[ℝ] Matrix (Fin n) (Fin n) ℂ) →ₗ⁅ℂ⁆ Module.End ℂ V)

/-- `π(1 ⊗ [D, X]) = [π(1 ⊗ D), π(1 ⊗ X)]`. -/
theorem complex_map_commutator (D X : Matrix (Fin n) (Fin n) ℂ) :
    π (1 ⊗ₜ (D * X - X * D)) = π (1 ⊗ₜ D) * π (1 ⊗ₜ X) - π (1 ⊗ₜ X) * π (1 ⊗ₜ D) := by
  calc π (1 ⊗ₜ (D * X - X * D))
      = π ⁅(1 : ℂ) ⊗ₜ[ℝ] D, (1 : ℂ) ⊗ₜ[ℝ] X⁆ := by
        rw [LieAlgebra.ExtendScalars.bracket_tmul, mul_one, Ring.lie_def]
    _ = ⁅π (1 ⊗ₜ D), π (1 ⊗ₜ X)⁆ := LieHom.map_lie π _ _
    _ = _ := Ring.lie_def _ _

/-- The diagonal directions `E_jj` (`c = 1`) and `i E_jj` (`c = i`). -/
abbrev diagDirection (p : Bool × Fin n) : Matrix (Fin n) (Fin n) ℂ :=
  Matrix.single p.2 p.2 (cond p.1 Complex.I 1)

theorem single_mul_strict_sub_mem (j : Fin n) (c : ℂ) (X : Matrix (Fin n) (Fin n) ℂ)
    (hX : ∀ i k : Fin n, (k : ℕ) ≤ i → X i k = 0) :
    ∀ i k : Fin n, (k : ℕ) ≤ i →
      (Matrix.single j j c * X - X * Matrix.single j j c) i k = 0 := by
  intro i k hik
  have h1 : (Matrix.single j j c * X) i k = 0 := by
    by_cases hij : i = j
    · subst hij
      rw [Matrix.single_mul_apply_same, hX i k hik, mul_zero]
    · exact Matrix.single_mul_apply_of_ne c j j i k hij X
  have h2 : (X * Matrix.single j j c) i k = 0 := by
    by_cases hkj : k = j
    · subst hkj
      rw [Matrix.mul_single_apply_same, hX i k hik, zero_mul]
    · exact Matrix.mul_single_apply_of_ne c j j i k hkj X
  rw [Matrix.sub_apply, h1, h2, sub_zero]

theorem mem_complexJacquetSubspace {X : Matrix (Fin n) (Fin n) ℂ}
    (hX : ∀ i j : Fin n, (j : ℕ) ≤ i → X i j = 0) (v : V) :
    π (1 ⊗ₜ X) v ∈ complexJacquetSubspace n π :=
  Submodule.subset_span ⟨X, v, hX, rfl⟩

theorem diag_mem_complexJacquetSubspace (j : Fin n) (c : ℂ) :
    ∀ w ∈ complexJacquetSubspace n π,
      π (1 ⊗ₜ Matrix.single j j c) w ∈ complexJacquetSubspace n π := by
  intro w hw
  induction hw using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨X, v, hX, rfl⟩ := hx
    have h := congrArg (fun f : Module.End ℂ V => f v)
      (complex_map_commutator π (Matrix.single j j c) X)
    simp only [LinearMap.sub_apply, Module.End.mul_apply] at h
    have h' : π (1 ⊗ₜ Matrix.single j j c) (π (1 ⊗ₜ X) v) =
        π (1 ⊗ₜ (Matrix.single j j c * X - X * Matrix.single j j c)) v +
          π (1 ⊗ₜ X) (π (1 ⊗ₜ Matrix.single j j c) v) := by
      rw [h]; abel
    rw [h']
    exact Submodule.add_mem _
      (mem_complexJacquetSubspace π (single_mul_strict_sub_mem j c X hX) v)
      (mem_complexJacquetSubspace π hX _)
  | zero => simp
  | add x y _ _ hx hy => rw [map_add]; exact Submodule.add_mem _ hx hy
  | smul r x _ hx => rw [map_smul]; exact Submodule.smul_mem _ r hx

theorem diagDirection_commute (p q : Bool × Fin n) :
    diagDirection p * diagDirection q = diagDirection q * diagDirection p := by
  unfold diagDirection
  by_cases h : p.2 = q.2
  · rw [h, Matrix.single_mul_single_same, Matrix.single_mul_single_same, mul_comm]
  · rw [Matrix.single_mul_single_of_ne _ _ _ _ h,
      Matrix.single_mul_single_of_ne _ _ _ _ (Ne.symm h)]

theorem diagDirection_map_commute (p q : Bool × Fin n) (v : V) :
    π (1 ⊗ₜ diagDirection p) (π (1 ⊗ₜ diagDirection q) v) =
      π (1 ⊗ₜ diagDirection q) (π (1 ⊗ₜ diagDirection p) v) := by
  have h := LinearMap.congr_fun (complex_map_commutator π (diagDirection p) (diagDirection q)) v
  rw [diagDirection_commute p q, sub_self, TensorProduct.tmul_zero, map_zero] at h
  simp only [LinearMap.zero_apply, LinearMap.sub_apply, Module.End.mul_apply] at h
  exact (sub_eq_zero.mp h.symm)

/-- The diagonal direction `p` acting on the Jacquet module `V/𝔫V`. -/
def jacquetDiagOp (p : Bool × Fin n) : Module.End ℂ (V ⧸ complexJacquetSubspace n π) :=
  (complexJacquetSubspace n π).mapQ (complexJacquetSubspace n π) (π (1 ⊗ₜ diagDirection p))
    (fun w hw => diag_mem_complexJacquetSubspace π p.2 _ w hw)

theorem jacquetDiagOp_mkQ (p : Bool × Fin n) (v : V) :
    jacquetDiagOp π p ((complexJacquetSubspace n π).mkQ v) =
      (complexJacquetSubspace n π).mkQ (π (1 ⊗ₜ diagDirection p) v) := rfl

theorem jacquetDiagOp_commute (p q : Bool × Fin n) :
    Commute (jacquetDiagOp π p) (jacquetDiagOp π q) := by
  apply Submodule.linearMap_qext
  apply LinearMap.ext
  intro v
  change jacquetDiagOp π p (jacquetDiagOp π q ((complexJacquetSubspace n π).mkQ v)) =
    jacquetDiagOp π q (jacquetDiagOp π p ((complexJacquetSubspace n π).mkQ v))
  rw [jacquetDiagOp_mkQ, jacquetDiagOp_mkQ, jacquetDiagOp_mkQ, jacquetDiagOp_mkQ,
    diagDirection_map_commute]

/-- The transposed action on the dual of the Jacquet module. -/
def jacquetDualOp (p : Bool × Fin n) :
    Module.End ℂ (Module.Dual ℂ (V ⧸ complexJacquetSubspace n π)) :=
  (jacquetDiagOp π p).dualMap

theorem jacquetDualOp_commute (p q : Bool × Fin n) :
    Commute (jacquetDualOp π p) (jacquetDualOp π q) := by
  change (jacquetDiagOp π p).dualMap ∘ₗ (jacquetDiagOp π q).dualMap =
    (jacquetDiagOp π q).dualMap ∘ₗ (jacquetDiagOp π p).dualMap
  rw [LinearMap.dualMap_comp_dualMap, LinearMap.dualMap_comp_dualMap]
  exact congrArg LinearMap.dualMap (jacquetDiagOp_commute π q p).eq

theorem comp_mkQ_ne_zero {ℓ : Module.Dual ℂ (V ⧸ complexJacquetSubspace n π)} (hℓ : ℓ ≠ 0) :
    ℓ ∘ₗ (complexJacquetSubspace n π).mkQ ≠ 0 := by
  intro h
  apply hℓ
  apply Submodule.linearMap_qext
  rw [h, LinearMap.zero_comp]

/-- A common eigenvector of the transposed diagonal action gives a Jacquet functional. -/
theorem isComplexJacquetFunctional_of_eigen
    (ℓ : Module.Dual ℂ (V ⧸ complexJacquetSubspace n π)) (c : Bool × Fin n → ℂ)
    (hc : ∀ p, jacquetDualOp π p ℓ = c p • ℓ) :
    IsComplexJacquetFunctional n π (ℓ ∘ₗ (complexJacquetSubspace n π).mkQ)
      (fun j => c (false, j)) (fun j => c (true, j)) := by
  have key : ∀ p v, ℓ ((complexJacquetSubspace n π).mkQ (π (1 ⊗ₜ diagDirection p) v)) =
      c p * ℓ ((complexJacquetSubspace n π).mkQ v) := by
    intro p v
    have h := LinearMap.congr_fun (hc p) ((complexJacquetSubspace n π).mkQ v)
    rw [jacquetDualOp, LinearMap.dualMap_apply, jacquetDiagOp_mkQ] at h
    simpa using h
  refine ⟨fun X hX v => ?_, fun j v => ⟨key (false, j) v, key (true, j) v⟩⟩
  rw [LinearMap.comp_apply, Submodule.mkQ_apply,
    (Submodule.Quotient.mk_eq_zero _).mpr (mem_complexJacquetSubspace π hX v), map_zero]

/-- A Jacquet functional factors through `V/𝔫V`, where its transpose is an eigenvector. -/
theorem exists_eigen_of_isComplexJacquetFunctional {ℓ : V →ₗ[ℂ] ℂ} {a b : Fin n → ℂ}
    (hℓ : IsComplexJacquetFunctional n π ℓ a b) :
    ∃ ℓ' : Module.Dual ℂ (V ⧸ complexJacquetSubspace n π),
      ℓ = ℓ' ∘ₗ (complexJacquetSubspace n π).mkQ ∧
        ∀ j, jacquetDualOp π (false, j) ℓ' = a j • ℓ' := by
  have hker : complexJacquetSubspace n π ≤ LinearMap.ker ℓ := by
    refine Submodule.span_le.mpr ?_
    rintro _ ⟨X, v, hX, rfl⟩
    exact hℓ.1 X hX v
  refine ⟨(complexJacquetSubspace n π).liftQ ℓ hker,
    ((complexJacquetSubspace n π).liftQ_mkQ ℓ hker).symm, fun j => ?_⟩
  apply Submodule.linearMap_qext
  apply LinearMap.ext
  intro v
  simp only [LinearMap.comp_apply, jacquetDualOp, LinearMap.dualMap_apply,
    Submodule.mkQ_apply, Submodule.liftQ_apply, LinearMap.smul_apply, smul_eq_mul]
  exact (hℓ.2 j v).1

end Reduction

/-- Proof of the reduction. By Casselman's theorem `V/𝔫V` is finite-dimensional and nonzero.
The diagonal directions act on it by commuting operators, so their transposes have a common
eigenvector, a nonzero Jacquet functional. Every exponent `a_j` of a nonzero Jacquet functional
is an eigenvalue of the transposed action of `E_jj`, so only finitely many exponent tuples occur.
Choose one minimizing `P(a) = ∑_k (n - k) Re a_k`. If it were not ordered, some adjacent pair
`(i, i + 1)` would have `Re a_{i+1} + 2 < Re a_i`; the rank-one step then gives exponents `a'`
with `P(a') - P(a) = Re a'_i - Re a_i < 0`, a contradiction. -/
theorem complexOrderedJacquetReduction : ComplexOrderedJacquetReductionStatement.{uV} := by
  intro hA hB n V _ _ ρ π hgk hirr hadm
  classical
  obtain ⟨hfin, hne⟩ := hA n V ρ π hgk hirr hadm
  have := hfin
  have : Nontrivial (V ⧸ complexJacquetSubspace n π) :=
    Submodule.Quotient.nontrivial_iff.mpr hne
  -- The exponents of nonzero Jacquet functionals.
  set E : Set (Fin n → ℂ) := {a | ∃ (ℓ : V →ₗ[ℂ] ℂ) (b : Fin n → ℂ), ℓ ≠ 0 ∧
    IsComplexJacquetFunctional n π ℓ a b} with hE
  have hEfin : E.Finite := by
    refine (Set.Finite.pi (t := fun j => {c | (jacquetDualOp π (false, j)).HasEigenvalue c})
      fun j => Module.End.finite_hasEigenvalue _).subset ?_
    rintro a ⟨ℓ, b, hℓ0, hℓ⟩
    obtain ⟨ℓ', rfl, hℓ'⟩ := exists_eigen_of_isComplexJacquetFunctional π hℓ
    have hℓ'0 : ℓ' ≠ 0 := by
      rintro rfl
      exact hℓ0 (LinearMap.zero_comp _)
    intro j _
    exact Module.End.hasEigenvalue_of_hasEigenvector
      (Module.End.hasEigenvector_iff.mpr ⟨Module.End.mem_eigenspace_iff.mpr (hℓ' j), hℓ'0⟩)
  have hEne : E.Nonempty := by
    obtain ⟨x, hx⟩ := exists_ne (0 : Module.Dual ℂ (V ⧸ complexJacquetSubspace n π))
    obtain ⟨w, -, hw0, hw⟩ := exists_common_eigenvector_of_commute (jacquetDualOp π)
      (jacquetDualOp_commute π) Finset.univ ⊤ inferInstance
      ((Submodule.ne_bot_iff _).mpr ⟨x, trivial, hx⟩) (fun _ _ _ => trivial)
    choose c hc using fun p => hw p (Finset.mem_univ p)
    exact ⟨_, _, _, comp_mkQ_ne_zero π hw0, isComplexJacquetFunctional_of_eigen π w c hc⟩
  -- Minimize the potential.
  set P : (Fin n → ℂ) → ℝ := fun a => ∑ k : Fin n, ((n : ℝ) - ((k : ℕ) : ℝ)) * (a k).re
    with hP
  obtain ⟨a, ⟨ℓ, b, hℓ0, hℓ⟩, hmin⟩ := Set.exists_min_image E P hEfin hEne
  refine ⟨ℓ, a, b, hℓ0, hℓ, ?_⟩
  apply fin_le_of_adjacent_le (fun k => (a k).re + 2 * ((k : ℕ) : ℝ))
  intro i j hij
  have hjr : ((j : ℕ) : ℝ) = ((i : ℕ) : ℝ) + 1 := by rw [hij]; push_cast; ring
  by_contra hlt
  have hlt' : (a j).re + 2 < (a i).re := by
    rw [hjr] at hlt
    linarith [not_le.mp hlt]
  obtain ⟨ℓ', a', b', hℓ'0, hℓ', hoff, hsum, hord⟩ :=
    hB n V ρ π hgk hirr hadm ℓ a b hℓ0 hℓ i j hij hlt'
  have hPle := hmin a' ⟨ℓ', b', hℓ'0, hℓ'⟩
  have hij' : i ≠ j := fun h => by rw [h] at hij; omega
  have hdiff : P a' - P a = ((n : ℝ) - ((i : ℕ) : ℝ)) * ((a' i).re - (a i).re) +
      ((n : ℝ) - ((j : ℕ) : ℝ)) * ((a' j).re - (a j).re) := by
    simp only [hP]
    rw [← Finset.sum_sub_distrib,
      Finset.sum_eq_add_of_mem i j (Finset.mem_univ _) (Finset.mem_univ _) hij']
    · ring
    · intro k _ hk
      rw [hoff k hk.1 hk.2, sub_self]
  have hre : (a' i).re + (a' j).re = (a i).re + (a j).re := by
    have := congrArg Complex.re hsum
    simpa using this
  have hdiff' : P a' - P a = (a' i).re - (a i).re := by
    rw [hdiff, hjr]
    linear_combination ((n : ℝ) - ((i : ℕ) : ℝ) - 1) * hre
  linarith

end Langlands.Archimedean
