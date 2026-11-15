import Langlands.Representation.Archimedean.RealJacquetFiniteDimensional
import Langlands.Representation.Archimedean.RealGKInfinitesimalCharacter
import Mathlib.RingTheory.MvPolynomial.Symmetric.NewtonIdentities
import Mathlib.RingTheory.Polynomial.Vieta
import Mathlib.RingTheory.MvPolynomial.Homogeneous
import Mathlib.Analysis.Normed.Algebra.MatrixExponential
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Topology.Instances.Matrix

noncomputable section

open scoped TensorProduct Matrix

set_option autoImplicit false

namespace Langlands.Archimedean

namespace RealJacquetFiniteGeneration

attribute [local instance 100] LieRing.ofAssociativeRing

universe uV

/-! ## Powers of a variable modulo the power sums -/

section Poly

open MvPolynomial

variable (n : ℕ)

/-- `J d`: the span of the products `x^γ · p_l` with `l ≥ 1` and `|γ| + l = d`, where
`p_l = ∑ᵢ Xᵢ^l` is the `l`-th power sum. -/
def powerSumSpan (d : ℕ) : Submodule ℂ (MvPolynomial (Fin n) ℂ) :=
  Submodule.span ℂ {p | ∃ (γ : Fin n →₀ ℕ) (l : ℕ), 1 ≤ l ∧ γ.degree + l = d ∧
    p = monomial γ 1 * psum (Fin n) ℂ l}

variable {n}

theorem monomial_mul_mem_powerSumSpan (γ : Fin n →₀ ℕ) {d : ℕ} {p : MvPolynomial (Fin n) ℂ}
    (hp : p ∈ powerSumSpan n d) : monomial γ 1 * p ∈ powerSumSpan n (γ.degree + d) := by
  induction hp using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨γ', l, hl, hdeg, rfl⟩ := hx
    refine Submodule.subset_span ⟨γ + γ', l, hl, ?_, ?_⟩
    · rw [map_add]; omega
    · rw [← mul_assoc, monomial_mul_monomial, one_mul]
  | zero => simp
  | add x y _ _ hx hy => rw [mul_add]; exact add_mem hx hy
  | smul c x _ hx => rw [mul_smul_comm]; exact Submodule.smul_mem _ c hx

theorem mul_psum_mem_powerSumSpan {p : MvPolynomial (Fin n) ℂ} {k l : ℕ}
    (hp : MvPolynomial.IsHomogeneous p k)
    (hl : 1 ≤ l) : p * psum (Fin n) ℂ l ∈ powerSumSpan n (k + l) := by
  rw [p.as_sum, Finset.sum_mul]
  refine Submodule.sum_mem _ fun γ hγ => ?_
  have hdeg : γ.degree = k := by
    have := hp (mem_support_iff.1 hγ)
    rw [Finsupp.degree_eq_weight_one (R := ℕ)]; exact this
  have : monomial γ (p.coeff γ) = p.coeff γ • monomial γ (1 : ℂ) := by
    rw [smul_monomial, smul_eq_mul, mul_one]
  rw [this, smul_mul_assoc]
  exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨γ, l, hl, by rw [hdeg], rfl⟩)

theorem esymm_isHomogeneous (k : ℕ) : MvPolynomial.IsHomogeneous (esymm (Fin n) ℂ k) k := by
  refine MvPolynomial.IsHomogeneous.sum _ _ _ fun t ht => ?_
  have h := MvPolynomial.IsHomogeneous.prod t (fun i => (X i : MvPolynomial (Fin n) ℂ)) (fun _ => 1)
    (fun i _ => isHomogeneous_X ℂ i)
  rw [Finset.mem_powersetCard] at ht
  simpa [ht.2] using h

theorem esymm_mem_powerSumSpan {k : ℕ} (hk : 1 ≤ k) :
    esymm (Fin n) ℂ k ∈ powerSumSpan n k := by
  have hmem : (k : MvPolynomial (Fin n) ℂ) * esymm (Fin n) ℂ k ∈ powerSumSpan n k := by
    rw [mul_esymm_eq_sum, Finset.mul_sum]
    refine Submodule.sum_mem _ fun a ha => ?_
    rw [Finset.mem_filter, Finset.mem_antidiagonal] at ha
    have hhom : MvPolynomial.IsHomogeneous ((-1 : MvPolynomial (Fin n) ℂ) ^ (k + 1) *
        ((-1) ^ a.1 * esymm (Fin n) ℂ a.1)) a.1 := by
      have h1 : ((-1 : MvPolynomial (Fin n) ℂ) ^ (k + 1) * (-1) ^ a.1) =
          C ((-1 : ℂ) ^ (k + 1) * (-1) ^ a.1) := by simp
      rw [← mul_assoc, h1]
      exact MvPolynomial.IsHomogeneous.C_mul (esymm_isHomogeneous a.1) _
    have := mul_psum_mem_powerSumSpan hhom (l := a.2) (by omega)
    rw [ha.1] at this
    simpa only [mul_assoc] using this
  have hk' : (k : ℂ) ≠ 0 := by exact_mod_cast (show k ≠ 0 by omega)
  have : esymm (Fin n) ℂ k = (k : ℂ)⁻¹ • ((k : MvPolynomial (Fin n) ℂ) * esymm (Fin n) ℂ k) := by
    rw [← map_natCast (C : ℂ →+* MvPolynomial (Fin n) ℂ), ← smul_eq_C_mul, smul_smul,
      inv_mul_cancel₀ hk', one_smul]
  rw [this]
  exact Submodule.smul_mem _ _ hmem

/-- `Xᵢⁿ ∈ J n`: by Vieta, `∏ⱼ (Xⱼ - Xᵢ) = 0` expands to `(-Xᵢ)ⁿ + ∑_{j ≥ 1} eⱼ (-Xᵢ)^{n-j}`,
and `eⱼ ∈ J j` by Newton's identities. -/
theorem X_pow_mem_powerSumSpan (i : Fin n) : X i ^ n ∈ powerSumSpan n n := by
  have hV := congrArg (Polynomial.eval (-X i)) (MvPolynomial.prod_C_add_X_eq_sum_esymm ℂ (Fin n))
  rw [Polynomial.eval_prod, Finset.prod_eq_zero (Finset.mem_univ i) (by simp),
    Polynomial.eval_finsetSum, Fintype.card_fin, Finset.sum_range_succ'] at hV
  simp only [Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X,
    esymm_zero, one_mul, Nat.sub_zero] at hV
  have hsum : ∑ j ∈ Finset.range n, esymm (Fin n) ℂ (j + 1) * (-X i) ^ (n - (j + 1)) ∈
      powerSumSpan n n := by
    refine Submodule.sum_mem _ fun j hj => ?_
    rw [Finset.mem_range] at hj
    have h1 : (-X i : MvPolynomial (Fin n) ℂ) ^ (n - (j + 1)) =
        ((-1 : ℂ) ^ (n - (j + 1))) • monomial (Finsupp.single i (n - (j + 1))) 1 := by
      rw [neg_pow, ← X_pow_eq_monomial, smul_eq_C_mul]
      simp
    rw [h1, mul_smul_comm, mul_comm]
    refine Submodule.smul_mem _ _ ?_
    have := monomial_mul_mem_powerSumSpan (Finsupp.single i (n - (j + 1)))
      (esymm_mem_powerSumSpan (n := n) (k := j + 1) (by omega))
    rwa [Finsupp.degree_single, show n - (j + 1) + (j + 1) = n by omega] at this
  have hneg : (-X i : MvPolynomial (Fin n) ℂ) ^ n ∈ powerSumSpan n n := by
    have : (-X i : MvPolynomial (Fin n) ℂ) ^ n = -∑ j ∈ Finset.range n,
        esymm (Fin n) ℂ (j + 1) * (-X i) ^ (n - (j + 1)) := by
      rw [eq_neg_iff_add_eq_zero, add_comm]; exact hV.symm
    rw [this]; exact neg_mem hsum
  have : (X i : MvPolynomial (Fin n) ℂ) ^ n = ((-1 : ℂ) ^ n) • (-X i) ^ n := by
    rw [smul_eq_C_mul, map_pow, map_neg, map_one, ← mul_pow, neg_one_mul, neg_neg]
  rw [this]
  exact Submodule.smul_mem _ _ hneg

/-- A monomial of degree `d` with some exponent `≥ n` lies in `J d`. -/
theorem monomial_mem_powerSumSpan {α : Fin n →₀ ℕ} {i : Fin n} (hi : n ≤ α i) :
    monomial α (1 : ℂ) ∈ powerSumSpan n α.degree := by
  have hle : Finsupp.single i n ≤ α := by
    rw [Finsupp.single_le_iff]; exact hi
  have hα : α = (α - Finsupp.single i n) + Finsupp.single i n := (tsub_add_cancel_of_le hle).symm
  have := monomial_mul_mem_powerSumSpan (α - Finsupp.single i n) (X_pow_mem_powerSumSpan i)
  rw [X_pow_eq_monomial, monomial_mul_monomial, one_mul, ← hα] at this
  convert this using 2
  conv_lhs => rw [hα]
  rw [map_add, Finsupp.degree_single]

end Poly

/-! ## The operators `φ(1 ⊗ X)` -/

section Op

/-- Real `n × n` matrices. -/
abbrev Mat (n : ℕ) := Matrix (Fin n) (Fin n) ℝ

/-- The matrix unit `E a b`. -/
abbrev E {n : ℕ} (a b : Fin n) : Mat n := Matrix.single a b 1

/-- The diagonal matrix unit `D i = E i i`. -/
abbrev D {n : ℕ} (i : Fin n) : Mat n := E i i

variable {n : ℕ} {B : Type*} [Ring B] [Algebra ℂ B]

/-- `op φ X = φ(1 ⊗ X)` for a real matrix `X`. -/
def op (φ : (ℂ ⊗[ℝ] Mat n) →ₗ⁅ℂ⁆ B) (X : Mat n) : B := φ (1 ⊗ₜ X)

variable (φ : (ℂ ⊗[ℝ] Mat n) →ₗ⁅ℂ⁆ B)

theorem op_tmul (c : ℂ) (X : Mat n) : φ (c ⊗ₜ X) = c • op φ X := by
  rw [op, ← map_smul, TensorProduct.smul_tmul', smul_eq_mul, mul_one]

theorem op_add (X Y : Mat n) : op φ (X + Y) = op φ X + op φ Y := by
  simp only [op, TensorProduct.tmul_add, map_add]

theorem op_sub (X Y : Mat n) : op φ (X - Y) = op φ X - op φ Y := by
  simp only [op, TensorProduct.tmul_sub, map_sub]

theorem op_zero : op φ (0 : Mat n) = 0 := by
  simp only [op, TensorProduct.tmul_zero, map_zero]

theorem op_real_smul (r : ℝ) (X : Mat n) : op φ (r • X) = (r : ℂ) • op φ X := by
  rw [op, ← TensorProduct.smul_tmul, Complex.real_smul, mul_one, op_tmul]

theorem op_eq_sum (X : Mat n) : op φ X = ∑ a, ∑ b, (X a b : ℂ) • op φ (E a b) := by
  have h : X = ∑ a, ∑ b, X a b • E a b := by
    conv_lhs => rw [Matrix.matrix_eq_sum_single X]
    simp [E, Matrix.smul_single]
  conv_lhs => rw [h]
  simp only [op, TensorProduct.tmul_sum, map_sum]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  exact op_real_smul φ _ _

/-- `φ(1 ⊗ [X, Y]) = [φ(1 ⊗ X), φ(1 ⊗ Y)]`. -/
theorem op_commutator (X Y : Mat n) :
    op φ (X * Y - Y * X) = op φ X * op φ Y - op φ Y * op φ X := by
  calc φ (1 ⊗ₜ (X * Y - Y * X))
      = φ ⁅(1 : ℂ) ⊗ₜ[ℝ] X, (1 : ℂ) ⊗ₜ[ℝ] Y⁆ := by
        rw [LieAlgebra.ExtendScalars.bracket_tmul, mul_one, Ring.lie_def]
    _ = ⁅φ (1 ⊗ₜ X), φ (1 ⊗ₜ Y)⁆ := LieHom.map_lie φ _ _
    _ = _ := Ring.lie_def _ _

theorem E_mul_E_sub (a b i j : Fin n) :
    E a b * E i j - E i j * E a b =
      (if b = i then E a j else 0) - (if j = a then E i b else 0) := by
  rcases eq_or_ne b i with rfl | h1 <;> rcases eq_or_ne j a with rfl | h2 <;>
    simp [E, Matrix.single_mul_single_of_ne, *]

theorem op_E_commutator (a b i j : Fin n) :
    op φ (E a b) * op φ (E i j) - op φ (E i j) * op φ (E a b) =
      (if b = i then op φ (E a j) else 0) - (if j = a then op φ (E i b) else 0) := by
  rw [← op_commutator, E_mul_E_sub, op_sub]
  split_ifs <;> simp [op_zero]

end Op

/-! ## Gelfand's central elements -/

section Gelfand

/-- If the entries of a matrix `𝔈` over a ring satisfy the commutation relations of the matrix
units, then every entry commutes with `trace (𝔈 ^ l)`: the matrix `𝔈 a b • 1 - E b a`
commutes with `𝔈`. -/
theorem commute_trace_pow {B : Type*} [Ring B] {n : ℕ} (𝔈 : Matrix (Fin n) (Fin n) B)
    (hrel : ∀ a b i j, 𝔈 a b * 𝔈 i j - 𝔈 i j * 𝔈 a b =
      (if b = i then 𝔈 a j else 0) - (if j = a then 𝔈 i b else 0))
    (a b : Fin n) (l : ℕ) : Commute (𝔈 a b) (Matrix.trace (𝔈 ^ l)) := by
  set x := 𝔈 a b with hx
  let T : Matrix (Fin n) (Fin n) B := Matrix.diagonal (fun _ => x) - Matrix.single b a 1
  have h1 : ∀ i j, (Matrix.single b a (1 : B) * 𝔈) i j = if b = i then 𝔈 a j else 0 := by
    intro i j
    by_cases h : b = i
    · subst h; simp
    · rw [Matrix.single_mul_apply_of_ne _ _ _ _ _ (Ne.symm h)]; simp [h]
  have h2 : ∀ i j, (𝔈 * Matrix.single b a (1 : B)) i j = if j = a then 𝔈 i b else 0 := by
    intro i j
    by_cases h : j = a
    · subst h; simp
    · rw [Matrix.mul_single_apply_of_ne _ _ _ _ _ h]; simp [h]
  have hT : Commute T 𝔈 := by
    show T * 𝔈 = 𝔈 * T
    ext i j
    simp only [T, sub_mul, mul_sub, Matrix.sub_apply, Matrix.diagonal_mul, Matrix.mul_diagonal,
      h1, h2]
    rw [sub_eq_sub_iff_sub_eq_sub, hrel a b i j]
  have htr := congrArg Matrix.trace (hT.pow_right l).eq
  simp only [T, sub_mul, mul_sub, Matrix.trace_sub, Matrix.trace_single_mul,
    Matrix.trace_mul_single, one_smul, MulOpposite.op_one] at htr
  have hd1 : Matrix.trace (Matrix.diagonal (fun _ => x) * 𝔈 ^ l) = x * Matrix.trace (𝔈 ^ l) := by
    simp [Matrix.trace, Matrix.diagonal_mul, Finset.mul_sum]
  have hd2 : Matrix.trace (𝔈 ^ l * Matrix.diagonal (fun _ => x)) = Matrix.trace (𝔈 ^ l) * x := by
    simp [Matrix.trace, Matrix.mul_diagonal, Finset.sum_mul]
  rw [hd1, hd2, sub_left_inj] at htr
  exact htr

variable (n : ℕ)

/-- The universal enveloping algebra of `ℂ ⊗_ℝ 𝔤𝔩_n(ℝ)`. -/
abbrev UEnv := UniversalEnvelopingAlgebra ℂ (ℂ ⊗[ℝ] Mat n)

/-- The matrix of generators `ι(1 ⊗ E i j)` of `U(𝔤)`. -/
def gen : Matrix (Fin n) (Fin n) (UEnv n) :=
  Matrix.of fun i j => op (UniversalEnvelopingAlgebra.ι ℂ) (E i j)

/-- Gelfand's elements `trace (gen ^ l)` are central. -/
theorem trace_gen_pow_mem_center (l : ℕ) :
    Matrix.trace (gen n ^ l) ∈ Subalgebra.center ℂ (UEnv n) := by
  rw [Subalgebra.mem_center_iff]
  have hcomm : ∀ a b, Commute (gen n a b) (Matrix.trace (gen n ^ l)) := fun a b =>
    commute_trace_pow (gen n)
      (fun a b i j => op_E_commutator (UniversalEnvelopingAlgebra.ι ℂ) a b i j) a b l
  intro g
  induction g using InfinitesimalCharacter.envInduction with
  | algebraMap r => exact Algebra.commutes r _
  | ι x =>
    induction x using TensorProduct.inductionOn with
    | tmul c M =>
      rw [op_tmul, op_eq_sum]
      refine (Commute.smul_left (Commute.sum_left _ _ _ fun a _ =>
        Commute.sum_left _ _ _ fun b _ => Commute.smul_left (hcomm a b) _) c).eq
    | add x y hx hy => rw [map_add, add_mul, mul_add, hx, hy]
  | mul a b ha hb => rw [mul_assoc, hb, ← mul_assoc, ha, mul_assoc]
  | add a b ha hb => rw [add_mul, mul_add, ha, hb]

end Gelfand

/-! ## Words in the operators `π(1 ⊗ X)` -/

section Words

variable {n : ℕ} {V : Type*} [AddCommGroup V] [Module ℂ V]
  (π : (ℂ ⊗[ℝ] Mat n) →ₗ⁅ℂ⁆ Module.End ℂ V)

/-- `wordOp π [X₁, …, X_r] = π(1 ⊗ X₁) ⋯ π(1 ⊗ X_r)`. -/
def wordOp (w : List (Mat n)) : Module.End ℂ V := (w.map (op π)).prod

@[simp] theorem wordOp_nil : wordOp π [] = 1 := rfl

@[simp] theorem wordOp_cons (X : Mat n) (w : List (Mat n)) :
    wordOp π (X :: w) = op π X * wordOp π w := by
  simp [wordOp]

@[simp] theorem wordOp_append (u w : List (Mat n)) :
    wordOp π (u ++ w) = wordOp π u * wordOp π w := by
  simp [wordOp]

theorem wordOp_singleton (X : Mat n) : wordOp π [X] = op π X := by
  simp

theorem wordOp_replicate (l : ℕ) (X : Mat n) :
    wordOp π (List.replicate l X) = op π X ^ l := by
  simp [wordOp, List.map_replicate]

/-- The operators carrying `F` into `S`. -/
def carry (F S : Submodule ℂ V) : Submodule ℂ (Module.End ℂ V) where
  carrier := {A | ∀ f ∈ F, A f ∈ S}
  add_mem' {A B} hA hB f hf := by
    rw [LinearMap.add_apply]; exact S.add_mem (hA f hf) (hB f hf)
  zero_mem' f _ := by rw [LinearMap.zero_apply]; exact S.zero_mem
  smul_mem' c A hA f hf := by
    rw [LinearMap.smul_apply]; exact S.smul_mem c (hA f hf)

theorem mem_carry {F S : Submodule ℂ V} {A : Module.End ℂ V} :
    A ∈ carry F S ↔ ∀ f ∈ F, A f ∈ S := Iff.rfl

/-- Strictly upper triangular real matrices. -/
def IsStrictUpper (X : Mat n) : Prop := ∀ i j : Fin n, (j : ℕ) ≤ i → X i j = 0

/-- Permuting the letters of a word of length `d` changes its operator by a combination of
operators of words of length `d - 1`. -/
theorem wordOp_perm_sub_mem {𝒞 : Submodule ℂ (Module.End ℂ V)} {d : ℕ}
    (hyp : ∀ w : List (Mat n), w.length < d → wordOp π w ∈ 𝒞) {l₁ l₂ : List (Mat n)}
    (h : l₁.Perm l₂) : ∀ u : List (Mat n), u.length + l₁.length = d →
      wordOp π (u ++ l₁) - wordOp π (u ++ l₂) ∈ 𝒞 := by
  induction h with
  | nil => intro u _; simp
  | cons x _ ih =>
    intro u hu
    have := ih (u ++ [x]) (by simp at hu ⊢; omega)
    simpa [List.append_assoc] using this
  | swap x y l =>
    intro u hu
    have hmem := hyp (u ++ (y * x - x * y) :: l) (by simp at hu ⊢; omega)
    convert hmem using 1
    simp only [wordOp_append, wordOp_cons, op_commutator]
    noncomm_ring
  | trans h₁ _ ih₁ ih₂ =>
    intro u hu
    have h2 := ih₂ u (by rw [← h₁.length_eq]; exact hu)
    rw [← sub_add_sub_cancel]
    exact add_mem (ih₁ u hu) h2

variable {π} {F S : Submodule ℂ V} {d : ℕ}

/-- A word of length `d` with a strictly upper triangular letter carries `F` into `S`. -/
theorem wordOp_mem_carry_of_upper (hS : ∀ X : Mat n, IsStrictUpper X → ∀ u ∈ S, op π X u ∈ S)
    (hyp : ∀ w : List (Mat n), w.length < d → wordOp π w ∈ carry F S)
    {w : List (Mat n)} (hw : w.length = d) {X : Mat n} (hX : X ∈ w) (hXu : IsStrictUpper X) :
    wordOp π w ∈ carry F S := by
  have h1 := wordOp_perm_sub_mem π hyp (List.perm_cons_erase hX) [] (by simpa using hw)
  simp only [List.nil_append] at h1
  have hlen : (w.erase X).length < d := by
    have := List.length_pos_of_mem hX
    rw [List.length_erase_of_mem hX]; omega
  have h2 : wordOp π (X :: w.erase X) ∈ carry F S := by
    rw [wordOp_cons, mem_carry]
    intro f hf
    rw [Module.End.mul_apply]
    exact hS X hXu _ (hyp _ hlen f hf)
  have := add_mem h1 h2
  rwa [sub_add_cancel] at this

/-- A word of length `d` with an antisymmetric letter carries `F` into `S`, if `F` is stable
under antisymmetric letters. -/
theorem wordOp_mem_carry_of_skew (hF : ∀ Y : Mat n, Yᵀ = -Y → ∀ f ∈ F, op π Y f ∈ F)
    (hyp : ∀ w : List (Mat n), w.length < d → wordOp π w ∈ carry F S)
    {w : List (Mat n)} (hw : w.length = d) {Y : Mat n} (hY : Y ∈ w) (hYs : Yᵀ = -Y) :
    wordOp π w ∈ carry F S := by
  have hp : w.Perm (w.erase Y ++ [Y]) :=
    (List.perm_cons_erase hY).trans (List.perm_append_singleton Y _).symm
  have h1 := wordOp_perm_sub_mem π hyp hp [] (by simpa using hw)
  simp only [List.nil_append] at h1
  have hlen : (w.erase Y).length < d := by
    have := List.length_pos_of_mem hY
    rw [List.length_erase_of_mem hY]; omega
  have h2 : wordOp π (w.erase Y ++ [Y]) ∈ carry F S := by
    rw [wordOp_append, wordOp_singleton, mem_carry]
    intro f hf
    rw [Module.End.mul_apply]
    exact hyp _ hlen _ (hF Y hYs f hf)
  have := add_mem h1 h2
  rwa [sub_add_cancel] at this

/-- The strictly upper triangular part of `Z + Zᵀ`. -/
def upperPart (Z : Mat n) : Mat n := Matrix.of fun i j => if i < j then Z i j + Z j i else 0

theorem isStrictUpper_upperPart (Z : Mat n) : IsStrictUpper (upperPart Z) := by
  intro i j hij
  simp only [upperPart, Matrix.of_apply]
  exact ite_eq_right_iff.2 fun h => absurd h (not_lt.2 (Fin.le_iff_val_le_val.2 hij))

theorem transpose_sub_upperPart {Z : Mat n} (hZ : ∀ i, Z i i = 0) :
    (Z - upperPart Z)ᵀ = -(Z - upperPart Z) := by
  ext i j
  simp only [Matrix.transpose_apply, Matrix.sub_apply, Matrix.neg_apply, upperPart,
    Matrix.of_apply]
  rcases lt_trichotomy i j with h | rfl | h
  · simp [h, lt_asymm h]
  · simp [hZ]
  · simp [h, lt_asymm h]

/-- A word of length `d` with a letter of zero diagonal carries `F` into `S`. -/
theorem wordOp_mem_carry_of_zeroDiag
    (hS : ∀ X : Mat n, IsStrictUpper X → ∀ u ∈ S, op π X u ∈ S)
    (hF : ∀ Y : Mat n, Yᵀ = -Y → ∀ f ∈ F, op π Y f ∈ F)
    (hyp : ∀ w : List (Mat n), w.length < d → wordOp π w ∈ carry F S)
    {w : List (Mat n)} (hw : w.length = d) {Z : Mat n} (hZ : Z ∈ w) (hZd : ∀ i, Z i i = 0) :
    wordOp π w ∈ carry F S := by
  obtain ⟨u, v, rfl⟩ := List.append_of_mem hZ
  have hop : op π Z = op π (upperPart Z) + op π (Z - upperPart Z) := by
    rw [← op_add, add_sub_cancel]
  have hsplit : wordOp π (u ++ Z :: v) = wordOp π (u ++ upperPart Z :: v) +
      wordOp π (u ++ (Z - upperPart Z) :: v) := by
    simp only [wordOp_append, wordOp_cons, hop, add_mul, mul_add]
  rw [hsplit]
  exact add_mem
    (wordOp_mem_carry_of_upper hS hyp (by simpa using hw) (by simp) (isStrictUpper_upperPart Z))
    (wordOp_mem_carry_of_skew hF hyp (by simpa using hw) (by simp) (transpose_sub_upperPart hZd))

variable (π) in
theorem wordOp_eq_sum_E (u v : List (Mat n)) (X : Mat n) :
    wordOp π (u ++ X :: v) = ∑ a, ∑ b, (X a b : ℂ) • wordOp π (u ++ E a b :: v) := by
  simp only [wordOp_append, wordOp_cons]
  rw [op_eq_sum π X]
  simp only [Finset.mul_sum, Finset.sum_mul, mul_smul_comm, smul_mul_assoc]

theorem E_apply_self_of_ne {a b : Fin n} (hab : a ≠ b) (i : Fin n) : E a b i i = 0 := by
  show Matrix.single a b (1 : ℝ) i i = 0
  rw [Matrix.single_apply]
  exact ite_eq_right_iff.2 fun h => absurd (h.1.trans h.2.symm) hab

/-- Reduction to words in the diagonal matrix units: if all diagonal words of length `d` carry
`F` into `S`, so do all words of length `d` (expand each letter in matrix units, from left to
right). -/
theorem wordOp_mem_carry_of_diag_prefix
    (hS : ∀ X : Mat n, IsStrictUpper X → ∀ u ∈ S, op π X u ∈ S)
    (hF : ∀ Y : Mat n, Yᵀ = -Y → ∀ f ∈ F, op π Y f ∈ F)
    (hyp : ∀ w : List (Mat n), w.length < d → wordOp π w ∈ carry F S)
    (hdiag : ∀ idx : List (Fin n), idx.length = d → wordOp π (idx.map D) ∈ carry F S) :
    ∀ (u : List (Mat n)) (idx : List (Fin n)), idx.length + u.length = d →
      wordOp π (idx.map D ++ u) ∈ carry F S := by
  intro u
  induction u with
  | nil => intro idx h; simpa using hdiag idx (by simpa using h)
  | cons X u ih =>
    intro idx h
    rw [wordOp_eq_sum_E]
    refine Submodule.sum_mem _ fun a _ => Submodule.sum_mem _ fun b _ =>
      Submodule.smul_mem _ _ ?_
    rcases eq_or_ne a b with rfl | hab
    · have := ih (idx ++ [a]) (by simp at h ⊢; omega)
      simpa [List.map_append, List.append_assoc] using this
    · exact wordOp_mem_carry_of_zeroDiag hS hF hyp (by simp at h ⊢; omega) (by simp)
        (E_apply_self_of_ne hab)

end Words

/-! ## Diagonal words as polynomials -/

section Diag

open MvPolynomial
open scoped IsMulCommutative

variable {n : ℕ} {V : Type*} [AddCommGroup V] [Module ℂ V]
  (π : (ℂ ⊗[ℝ] Mat n) →ₗ⁅ℂ⁆ Module.End ℂ V)

theorem op_D_commute (i j : Fin n) : Commute (op π (D i)) (op π (D j)) := by
  have h : D i * D j - D j * D i = (0 : Mat n) := by
    rcases eq_or_ne i j with rfl | h
    · exact sub_self _
    · simp only [D, E]
      rw [Matrix.single_mul_single_of_ne (j := i) (k := j) (h := h),
        Matrix.single_mul_single_of_ne (j := j) (k := i) (h := h.symm), sub_self]
  have := op_commutator π (D i) (D j)
  rw [h, op_zero] at this
  exact sub_eq_zero.1 this.symm

/-- The operators `π(1 ⊗ Dᵢ)`. -/
def diagSet : Set (Module.End ℂ V) := Set.range fun i => op π (D i)

instance : IsMulCommutative (Algebra.adjoin ℂ (diagSet π)) :=
  Algebra.isMulCommutative_adjoin ℂ (by
    rintro _ ⟨i, rfl⟩ _ ⟨j, rfl⟩ _
    exact op_D_commute π i j)

/-- Evaluation of polynomials at the commuting operators `π(1 ⊗ Dᵢ)`. -/
def diagEval : MvPolynomial (Fin n) ℂ →ₐ[ℂ] Module.End ℂ V :=
  (Algebra.adjoin ℂ (diagSet π)).val.comp
    (MvPolynomial.aeval fun i => ⟨op π (D i), Algebra.subset_adjoin ⟨i, rfl⟩⟩)

@[simp] theorem diagEval_X (i : Fin n) : diagEval π (X i) = op π (D i) := by
  simp [diagEval]

theorem wordOp_map_D (idx : List (Fin n)) :
    wordOp π (idx.map D) = diagEval π ((idx.map X).prod) := by
  induction idx with
  | nil => simp
  | cons i idx ih => simp [ih]

theorem exists_monomial_of_list (idx : List (Fin n)) :
    ∃ γ : Fin n →₀ ℕ, γ.degree = idx.length ∧ (idx.map X).prod = monomial γ (1 : ℂ) := by
  induction idx with
  | nil => exact ⟨0, by simp, by simp⟩
  | cons i idx ih =>
    obtain ⟨γ, hγ, hp⟩ := ih
    refine ⟨Finsupp.single i 1 + γ, ?_, ?_⟩
    · rw [map_add, Finsupp.degree_single, hγ, List.length_cons]; ring
    · rw [List.map_cons, List.prod_cons, hp, ← pow_one (X i), X_pow_eq_monomial,
        monomial_mul_monomial, one_mul]

theorem exists_list_of_monomial (γ : Fin n →₀ ℕ) :
    ∃ idx : List (Fin n), idx.length = γ.degree ∧ (idx.map X).prod = monomial γ (1 : ℂ) := by
  induction γ using Finsupp.induction with
  | zero => exact ⟨[], by simp, by simp⟩
  | single_add a b f _ _ ih =>
    obtain ⟨idx, hl, hp⟩ := ih
    refine ⟨List.replicate b a ++ idx, ?_, ?_⟩
    · rw [List.length_append, List.length_replicate, hl, map_add, Finsupp.degree_single]
    · rw [List.map_append, List.prod_append, List.map_replicate, List.prod_replicate, hp,
        X_pow_eq_monomial, monomial_mul_monomial, one_mul]

/-- The span of `π(1 ⊗ D)^β F` over exponents `β` in the box `{0, …, n - 1}ⁿ`. -/
def boxSpace (F : Submodule ℂ V) : Submodule ℂ V :=
  ⨆ β : Fin n → Fin n,
    F.map (diagEval π (monomial (Finsupp.equivFunOnFinite.symm fun i => (β i : ℕ)) 1))

instance (F : Submodule ℂ V) [FiniteDimensional ℂ F] : FiniteDimensional ℂ (boxSpace π F) :=
  Submodule.finiteDimensional_iSup _

theorem mem_boxSpace {F : Submodule ℂ V} {α : Fin n →₀ ℕ} (hα : ∀ i, α i < n) {f : V}
    (hf : f ∈ F) : diagEval π (monomial α 1) f ∈ boxSpace π F := by
  have h : Finsupp.equivFunOnFinite.symm (fun i => ((⟨α i, hα i⟩ : Fin n) : ℕ)) = α :=
    Finsupp.equivFunOnFinite.symm_apply_apply α
  refine Submodule.mem_iSup_of_mem (fun i => (⟨α i, hα i⟩ : Fin n)) ?_
  rw [h]
  exact Submodule.mem_map_of_mem hf

theorem le_boxSpace (F : Submodule ℂ V) : F ≤ boxSpace π F := by
  intro f hf
  have := mem_boxSpace π (α := 0) (fun i => by
    have := i.pos; simp; omega) hf
  simpa using this

end Diag

/-! ## Words with a letter of zero diagonal -/

section ZeroDiag

open MvPolynomial

variable {n : ℕ} {V : Type*} [AddCommGroup V] [Module ℂ V]
  (π : (ℂ ⊗[ℝ] Mat n) →ₗ⁅ℂ⁆ Module.End ℂ V)

/-- The matrix `(π(1 ⊗ E i j))ᵢⱼ`. -/
def opMat : Matrix (Fin n) (Fin n) (Module.End ℂ V) := Matrix.of fun i j => op π (E i j)

/-- The span of the operators of words of length `l` with a letter of zero diagonal. -/
def zdSpan (l : ℕ) : Submodule ℂ (Module.End ℂ V) :=
  Submodule.span ℂ {A | ∃ w : List (Mat n), w.length = l ∧ (∃ X ∈ w, ∀ i, X i i = 0) ∧
    wordOp π w = A}

theorem wordOp_mem_zdSpan {w : List (Mat n)} {X : Mat n} (hX : X ∈ w) (hXd : ∀ i, X i i = 0) :
    wordOp π w ∈ zdSpan π w.length :=
  Submodule.subset_span ⟨w, rfl, ⟨X, hX, hXd⟩, rfl⟩

theorem mul_op_mem_zdSpan {l : ℕ} {A : Module.End ℂ V} (hA : A ∈ zdSpan π l) (Y : Mat n) :
    A * op π Y ∈ zdSpan π (l + 1) := by
  induction hA using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨w, hw, ⟨X, hX, hXd⟩, rfl⟩ := hx
    have := wordOp_mem_zdSpan π (w := w ++ [Y]) (by simp [hX]) hXd
    simpa [hw] using this
  | zero => simp
  | add x y _ _ hx hy => rw [add_mul]; exact add_mem hx hy
  | smul c x _ hx => rw [smul_mul_assoc]; exact Submodule.smul_mem _ c hx

theorem wordOp_mul_mem_zdSpan (u : List (Mat n)) {l : ℕ} {A : Module.End ℂ V}
    (hA : A ∈ zdSpan π l) : wordOp π u * A ∈ zdSpan π (u.length + l) := by
  induction hA using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨w, hw, ⟨X, hX, hXd⟩, rfl⟩ := hx
    have := wordOp_mem_zdSpan π (w := u ++ w) (by simp [hX]) hXd
    simpa [hw] using this
  | zero => simp
  | add x y _ _ hx hy => rw [mul_add]; exact add_mem hx hy
  | smul c x _ hx => rw [mul_smul_comm]; exact Submodule.smul_mem _ c hx

/-- `(π(1 ⊗ E)^l)ᵢⱼ ≡ δᵢⱼ π(1 ⊗ Dᵢ)^l` modulo words with a letter of zero diagonal. -/
theorem opMat_pow_sub_mem (l : ℕ) (i j : Fin n) :
    (opMat π ^ l) i j - (if i = j then op π (D i) ^ l else 0) ∈ zdSpan π l := by
  induction l generalizing j with
  | zero =>
    rcases eq_or_ne i j with rfl | h
    · simp
    · simp [Matrix.one_apply_ne h, h]
  | succ l ih =>
    have hsum : (opMat π ^ (l + 1)) i j = ∑ k, (opMat π ^ l) i k * op π (E k j) := by
      rw [pow_succ, Matrix.mul_apply]; rfl
    have hdecomp : (opMat π ^ (l + 1)) i j = ∑ k, ((opMat π ^ l) i k -
        (if i = k then op π (D i) ^ l else 0)) * op π (E k j) + op π (D i) ^ l * op π (E i j) := by
      rw [hsum]
      simp only [sub_mul, Finset.sum_sub_distrib, ite_mul, zero_mul, Finset.sum_ite_eq,
        Finset.mem_univ, ite_true]
      abel
    rw [hdecomp]
    have h1 : ∑ k, ((opMat π ^ l) i k - (if i = k then op π (D i) ^ l else 0)) *
        op π (E k j) ∈ zdSpan π (l + 1) :=
      Submodule.sum_mem _ fun k _ => mul_op_mem_zdSpan π (ih k) _
    rcases eq_or_ne i j with rfl | h
    · rw [ite_eq_left_of_eq_true _ _ (eq_self i), add_sub_assoc, ← pow_succ]
      simpa using h1
    · rw [ite_eq_right_of_eq_false _ _ (eq_false h), sub_zero]
      refine add_mem h1 ?_
      have := wordOp_mem_zdSpan π (w := List.replicate l (D i) ++ [E i j]) (X := E i j)
        (by simp) (E_apply_self_of_ne h)
      simpa [wordOp_replicate] using this

/-- Gelfand's elements act through `π` by `trace (opMat ^ l)`. -/
theorem envelopingAction_trace_gen_pow (l : ℕ) :
    envelopingAction π (Matrix.trace (gen n ^ l)) = Matrix.trace (opMat π ^ l) := by
  have hmap : (gen n).map (envelopingAction π) = opMat π := by
    ext i j
    simp [gen, opMat, op, envelopingAction]
  rw [← hmap, ← AlgHom.mapMatrix_apply, ← map_pow, AlgHom.mapMatrix_apply]
  simp [Matrix.trace, map_sum]

/-- With an infinitesimal character, the power sums of the `π(1 ⊗ Dᵢ)` are scalars modulo
words with a letter of zero diagonal. -/
theorem diagEval_psum (hinf : HasInfinitesimalCharacter π) (l : ℕ) :
    ∃ c : ℂ, ∃ Z ∈ zdSpan π l, diagEval π (psum (Fin n) ℂ l) = c • 1 - Z := by
  obtain ⟨c, hc⟩ := hinf _ (trace_gen_pow_mem_center n l)
  rw [envelopingAction_trace_gen_pow, Algebra.algebraMap_eq_smul_one] at hc
  refine ⟨c, ∑ i, ((opMat π ^ l) i i - op π (D i) ^ l),
    Submodule.sum_mem _ fun i _ => by simpa using opMat_pow_sub_mem π l i i, ?_⟩
  rw [← hc]
  simp only [Matrix.trace, Matrix.diag_apply, Finset.sum_sub_distrib, sub_sub_cancel]
  simp [psum, map_sum]

end ZeroDiag

/-! ## Stability of `O(n)`-stable subspaces under antisymmetric letters

This section was written by Worker 725. -/

section SkewStability

open scoped Matrix.Norms.Operator

set_option backward.isDefEq.respectTransparency false

/-- The entries of a differentiable matrix-valued curve are differentiable. -/
theorem skew_hasDerivAt_entry {n : ℕ} {M : ℝ → Matrix (Fin n) (Fin n) ℝ}
    {M' : Matrix (Fin n) (Fin n) ℝ} {t : ℝ} (h : HasDerivAt M M' t) (i j : Fin n) :
    HasDerivAt (fun s => M s i j) (M' i j) t := by
  let L : Matrix (Fin n) (Fin n) ℝ →L[ℝ] ℝ := LinearMap.toContinuousLinearMap
    { toFun := fun A => A i j, map_add' := fun _ _ => rfl, map_smul' := fun _ _ => rfl }
  exact L.hasFDerivAt.comp_hasDerivAt t h

/-- The derivative of `t ↦ exp(t A)` at `0` is `A`. -/
theorem skew_hasDerivAt_exp_smul_zero {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) :
    HasDerivAt (fun t : ℝ => NormedSpace.exp (t • A)) A 0 := by
  have h := hasDerivAt_exp_smul_const (𝕂 := ℝ) A (0 : ℝ)
  simpa using h

/-- A real antisymmetric matrix is skew-adjoint. -/
theorem mem_skewAdjoint_of_transpose_eq_neg {n : ℕ} {Y : Matrix (Fin n) (Fin n) ℝ}
    (hY : Yᵀ = -Y) : Y ∈ skewAdjoint (Matrix (Fin n) (Fin n) ℝ) := by
  rw [skewAdjoint.mem_iff, Matrix.star_eq_conjTranspose,
    Matrix.conjTranspose_eq_transpose_of_trivial, hY]

/-- The one-parameter subgroup `t ↦ exp(t Y)` of `O(n)` for an antisymmetric real `Y`. -/
def skewCurve {n : ℕ} (Y : Matrix (Fin n) (Fin n) ℝ) (hY : Yᵀ = -Y) (t : ℝ) :
    Matrix.unitaryGroup (Fin n) ℝ :=
  ⟨NormedSpace.exp (t • Y), NormedSpace.exp_mem_unitary_of_mem_skewAdjoint
    (skewAdjoint.smul_mem t (mem_skewAdjoint_of_transpose_eq_neg hY))⟩

/-- A subspace stable under `ρ(O(n))` is stable under `π(1 ⊗ Y)` for every antisymmetric real
`Y`: differentiate `t ↦ ℓ(ρ(exp(tY)) f)`, which vanishes identically for every functional `ℓ`
vanishing on the subspace. -/
theorem apply_skew_mem_of_rho_stable {n : ℕ} {V : Type*} [AddCommGroup V] [Module ℂ V]
    {ρ : Representation ℂ (Matrix.unitaryGroup (Fin n) ℝ) V}
    {π : (ℂ ⊗[ℝ] Matrix (Fin n) (Fin n) ℝ) →ₗ⁅ℂ⁆ Module.End ℂ V}
    (hgk : IsRealGKModule n ρ π) (F : Submodule ℂ V)
    (hF : ∀ (k : Matrix.unitaryGroup (Fin n) ℝ), ∀ f ∈ F, ρ k f ∈ F)
    (Y : Matrix (Fin n) (Fin n) ℝ) (hY : Yᵀ = -Y) :
    ∀ f ∈ F, π (1 ⊗ₜ Y) f ∈ F := by
  intro f hf
  by_contra hnot
  obtain ⟨ℓ, hℓ, hFℓ⟩ := Submodule.exists_le_ker_of_notMem hnot
  have h0 : skewCurve Y hY 0 = 1 := by
    apply Subtype.ext
    simp [skewCurve]
  have hentry : ∀ i j, HasDerivAt
      (fun t => (skewCurve Y hY t : Matrix (Fin n) (Fin n) ℝ) i j) (Y i j) 0 :=
    fun i j => skew_hasDerivAt_entry (skew_hasDerivAt_exp_smul_zero Y) i j
  have hd := hgk.2.2.1 (skewCurve Y hY) Y h0 hentry f ℓ
  have hzero : (fun t => ℓ (ρ (skewCurve Y hY t) f)) = fun _ => (0 : ℂ) := by
    funext t
    exact hFℓ (hF _ f hf)
  rw [hzero] at hd
  exact hℓ (hd.unique (hasDerivAt_const (0 : ℝ) (0 : ℂ)))

end SkewStability

/-! ## All words carry `F` into `S` -/

section Carry

open MvPolynomial

variable {n : ℕ} {V : Type*} [AddCommGroup V] [Module ℂ V]
  {π : (ℂ ⊗[ℝ] Mat n) →ₗ⁅ℂ⁆ Module.End ℂ V} {F S : Submodule ℂ V} {d : ℕ}

/-- Under the induction hypothesis, words of length `d` with a letter of zero diagonal carry
`F` into `S`. -/
theorem zdSpan_le_carry
    (hS : ∀ X : Mat n, IsStrictUpper X → ∀ u ∈ S, op π X u ∈ S)
    (hF : ∀ Y : Mat n, Yᵀ = -Y → ∀ f ∈ F, op π Y f ∈ F)
    (hyp : ∀ w : List (Mat n), w.length < d → wordOp π w ∈ carry F S) :
    zdSpan π d ≤ carry F S := by
  rw [zdSpan, Submodule.span_le]
  rintro _ ⟨w, hw, ⟨X, hX, hXd⟩, rfl⟩
  exact wordOp_mem_carry_of_zeroDiag hS hF hyp hw hX hXd

/-- Under the induction hypothesis, `p(π(1 ⊗ D))` carries `F` into `S` for `p ∈ J d`. -/
theorem diagEval_mem_carry_of_mem_powerSumSpan (hinf : HasInfinitesimalCharacter π)
    (hS : ∀ X : Mat n, IsStrictUpper X → ∀ u ∈ S, op π X u ∈ S)
    (hF : ∀ Y : Mat n, Yᵀ = -Y → ∀ f ∈ F, op π Y f ∈ F)
    (hyp : ∀ w : List (Mat n), w.length < d → wordOp π w ∈ carry F S)
    {p : MvPolynomial (Fin n) ℂ} (hp : p ∈ powerSumSpan n d) :
    diagEval π p ∈ carry F S := by
  induction hp using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨γ, l, hl, hdeg, rfl⟩ := hx
    obtain ⟨idx, hlen, hprod⟩ := exists_list_of_monomial (n := n) γ
    obtain ⟨c, Z, hZ, hpsum⟩ := diagEval_psum π hinf l
    have hγ : diagEval π (monomial γ 1) = wordOp π (idx.map D) := by
      rw [wordOp_map_D, hprod]
    rw [map_mul, hpsum, hγ, mul_sub, mul_smul_comm, mul_one]
    refine sub_mem (Submodule.smul_mem _ _ (hyp _ (by rw [List.length_map]; omega))) ?_
    have := wordOp_mul_mem_zdSpan π (idx.map D) hZ
    rw [List.length_map, hlen, hdeg] at this
    exact zdSpan_le_carry hS hF hyp this
  | zero => rw [map_zero]; exact zero_mem _
  | add x y _ _ hx hy => rw [map_add]; exact add_mem hx hy
  | smul c x _ hx => rw [map_smul]; exact Submodule.smul_mem _ c hx

/-- Under the induction hypothesis, diagonal words of length `d` carry `F` into `S`, provided
`S` contains `boxSpace π F`. -/
theorem wordOp_diag_mem_carry (hinf : HasInfinitesimalCharacter π)
    (hS : ∀ X : Mat n, IsStrictUpper X → ∀ u ∈ S, op π X u ∈ S)
    (hF : ∀ Y : Mat n, Yᵀ = -Y → ∀ f ∈ F, op π Y f ∈ F)
    (hyp : ∀ w : List (Mat n), w.length < d → wordOp π w ∈ carry F S)
    (hbox : boxSpace π F ≤ S) (idx : List (Fin n)) (hidx : idx.length = d) :
    wordOp π (idx.map D) ∈ carry F S := by
  obtain ⟨γ, hγ, hprod⟩ := exists_monomial_of_list (n := n) idx
  rw [wordOp_map_D, hprod]
  by_cases hsmall : ∀ i, γ i < n
  · exact mem_carry.2 fun f hf => hbox (mem_boxSpace π hsmall hf)
  · simp only [not_forall, not_lt] at hsmall
    obtain ⟨i, hi⟩ := hsmall
    have := monomial_mem_powerSumSpan (n := n) hi
    rw [hγ, hidx] at this
    exact diagEval_mem_carry_of_mem_powerSumSpan hinf hS hF hyp this

/-- Every word carries `F` into `S`, if `S ⊇ boxSpace π F` is stable under `𝔫` and `F` is
stable under antisymmetric letters. -/
theorem wordOp_mem_carry (hinf : HasInfinitesimalCharacter π)
    (hS : ∀ X : Mat n, IsStrictUpper X → ∀ u ∈ S, op π X u ∈ S)
    (hF : ∀ Y : Mat n, Yᵀ = -Y → ∀ f ∈ F, op π Y f ∈ F)
    (hbox : boxSpace π F ≤ S) (w : List (Mat n)) : wordOp π w ∈ carry F S := by
  suffices h : ∀ m, ∀ w : List (Mat n), w.length = m → wordOp π w ∈ carry F S from h _ w rfl
  intro m
  induction m using Nat.strong_induction_on with
  | _ m ih =>
    have hyp : ∀ w : List (Mat n), w.length < m → wordOp π w ∈ carry F S :=
      fun w hw => ih _ hw w rfl
    intro w hw
    have := wordOp_mem_carry_of_diag_prefix hS hF hyp
      (fun idx hidx => wordOp_diag_mem_carry hinf hS hF hyp hbox idx hidx) w []
      (by simpa using hw)
    simpa using this

/-- `ρ(k) π(1 ⊗ X₁) ⋯ π(1 ⊗ X_r) = π(1 ⊗ k X₁ kᵀ) ⋯ π(1 ⊗ k X_r kᵀ) ρ(k)`. -/
theorem rho_wordOp {ρ : Representation ℂ (Matrix.unitaryGroup (Fin n) ℝ) V}
    (hgk : IsRealGKModule n ρ π) (k : Matrix.unitaryGroup (Fin n) ℝ) (w : List (Mat n))
    (x : V) : ρ k (wordOp π w x) =
      wordOp π (w.map fun X => (k : Mat n) * X * (star k : Mat n)) (ρ k x) := by
  induction w generalizing x with
  | nil => simp
  | cons X w ih =>
    simp only [wordOp_cons, List.map_cons, Module.End.mul_apply]
    simp only [op]
    rw [hgk.2.2.2, ih]

variable (π) in
/-- The span of the vectors `π(1 ⊗ X₁) ⋯ π(1 ⊗ X_r) f`, `f ∈ F`. -/
def wordSpan (F : Submodule ℂ V) : Submodule ℂ V :=
  Submodule.span ℂ {x | ∃ w : List (Mat n), ∃ f ∈ F, wordOp π w f = x}

theorem wordOp_apply_mem_wordSpan (w : List (Mat n)) {f : V} (hf : f ∈ F) :
    wordOp π w f ∈ wordSpan π F :=
  Submodule.subset_span ⟨w, f, hf, rfl⟩

theorem wordSpan_le {S : Submodule ℂ V} (h : ∀ w : List (Mat n), wordOp π w ∈ carry F S) :
    wordSpan π F ≤ S := by
  rw [wordSpan, Submodule.span_le]
  rintro _ ⟨w, f, hf, rfl⟩
  exact h w f hf

theorem op_apply_mem_wordSpan (M : Mat n) {x : V} (hx : x ∈ wordSpan π F) :
    op π M x ∈ wordSpan π F := by
  have hle : wordSpan π F ≤ (wordSpan π F).comap (op π M) := by
    rw [wordSpan, Submodule.span_le]
    rintro _ ⟨w, f, hf, rfl⟩
    rw [SetLike.mem_coe, Submodule.mem_comap, ← Module.End.mul_apply, ← wordOp_cons]
    exact wordOp_apply_mem_wordSpan _ hf
  exact hle hx

theorem apply_mem_wordSpan (X : ℂ ⊗[ℝ] Mat n) {x : V} (hx : x ∈ wordSpan π F) :
    π X x ∈ wordSpan π F := by
  induction X using TensorProduct.inductionOn generalizing x with
  | tmul c M =>
    rw [op_tmul, LinearMap.smul_apply]
    exact Submodule.smul_mem _ c (op_apply_mem_wordSpan M hx)
  | add X Y hX hY =>
    rw [map_add, LinearMap.add_apply]
    exact add_mem (hX hx) (hY hx)

theorem rho_mem_wordSpan {ρ : Representation ℂ (Matrix.unitaryGroup (Fin n) ℝ) V}
    (hgk : IsRealGKModule n ρ π) (hρF : ∀ (k : Matrix.unitaryGroup (Fin n) ℝ), ∀ f ∈ F, ρ k f ∈ F)
    (k : Matrix.unitaryGroup (Fin n) ℝ) {x : V} (hx : x ∈ wordSpan π F) :
    ρ k x ∈ wordSpan π F := by
  have hle : wordSpan π F ≤ (wordSpan π F).comap (ρ k) := by
    rw [wordSpan, Submodule.span_le]
    rintro _ ⟨w, f, hf, rfl⟩
    rw [SetLike.mem_coe, Submodule.mem_comap, rho_wordOp hgk]
    exact wordOp_apply_mem_wordSpan _ (hρF k f hf)
  exact hle hx

end Carry

/-- Finite generation over `U(𝔫)` of an irreducible admissible `(𝔤𝔩_n(ℝ), O(n))`-module:
`F = boxSpace π (orbitSpan ρ v)` for any nonzero `v`. -/
theorem realJacquetFiniteGeneration : RealJacquetFiniteGenerationStatement.{uV} := by
  intro n V _ _ ρ π hgk hirr hadm
  have hinf : HasInfinitesimalCharacter π :=
    InfinitesimalCharacter.realGKModuleInfinitesimalCharacter n V ρ π hgk hirr hadm
  have : Nontrivial V := hirr.1
  obtain ⟨v, hv⟩ := exists_ne (0 : V)
  have : FiniteDimensional ℂ (FiniteVectors.orbitSpan ρ v) := hgk.1 v
  refine ⟨boxSpace π (FiniteVectors.orbitSpan ρ v), inferInstance, fun S hFS hS => ?_⟩
  have hS' : ∀ X : Mat n, IsStrictUpper X → ∀ u ∈ S, op π X u ∈ S :=
    fun X hX u hu => hS X hX u hu
  have hρF : ∀ k : Matrix.unitaryGroup (Fin n) ℝ, ∀ f ∈ FiniteVectors.orbitSpan ρ v,
      ρ k f ∈ FiniteVectors.orbitSpan ρ v := fun k _ hf =>
    (FiniteVectors.orbitSubrepresentation ρ v).apply_mem_toSubmodule k hf
  have hF : ∀ Y : Mat n, Yᵀ = -Y → ∀ f ∈ FiniteVectors.orbitSpan ρ v,
      op π Y f ∈ FiniteVectors.orbitSpan ρ v := fun Y hY f hf =>
    apply_skew_mem_of_rho_stable hgk _ hρF Y hY f hf
  have hWS : wordSpan π (FiniteVectors.orbitSpan ρ v) ≤ S :=
    wordSpan_le (wordOp_mem_carry hinf hS' hF hFS)
  have hvW : v ∈ wordSpan π (FiniteVectors.orbitSpan ρ v) := by
    simpa using wordOp_apply_mem_wordSpan (π := π) [] (FiniteVectors.self_mem_orbitSpan ρ v)
  rcases hirr.2 _ (fun k x hx => rho_mem_wordSpan hgk hρF k hx)
      (fun X x hx => apply_mem_wordSpan X hx) with hbot | htop
  · rw [hbot, Submodule.mem_bot] at hvW
    exact absurd hvW hv
  · rw [htop] at hWS
    exact top_le_iff.1 hWS

end RealJacquetFiniteGeneration

end Langlands.Archimedean
