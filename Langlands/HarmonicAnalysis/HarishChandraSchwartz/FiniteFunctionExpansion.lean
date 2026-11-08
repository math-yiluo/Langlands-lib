import Langlands.HarmonicAnalysis.HarishChandraSchwartz.WeakConstantTermUniqueness
import Langlands.HarmonicAnalysis.GroupAction
import Langlands.Representation.IntegerLattice.GeneralizedWeightPolynomialComparisonProof
import Langlands.Representation.IntegerLattice.OccurringCharactersProof
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.FieldTheory.Separable
import Mathlib.LinearAlgebra.Eigenspace.Pi
import Mathlib.LinearAlgebra.Eigenspace.Semisimple
import Mathlib.LinearAlgebra.Eigenspace.Triangularizable
import Mathlib.LinearAlgebra.Semisimple
import Mathlib.Topology.Algebra.OpenSubgroup

/-! # Finite functions on `A_M` (Waldspurger, I.2)

Waldspurger, I.2 (printed pp. 242–243): a function `f` on `A_M` whose right translates span a
finite-dimensional space `V_f` is a finite sum `f(a) = ∑_{χ ∈ X} χ(a) P_χ(H_M(a))` of characters
times polynomials, and the polynomial growth `|f(a)| ≤ C (1 + σ(a))^n` is equivalent to
`Re(χ) = 0` for the characters of a minimal `X`.

This module proves, for an abstract commutative group `A` (the source's `A_M`) with an additive
map `H_M : A → E` to a real vector space, a lattice section `s : ℤ^d → A` with linear coordinates
`ℓ_i` on `E` (`ℓ_i(H_M(s(n))) = n_i`) and `A = ker(H_M) · s(ℤ^d)`, and with `ker(H_M)` acting on
`V_f` with finite orders (the smoothness of `f` together with the compactness of `A_M^1` in the
source):

* the expansion `f = exponentialPolynomial H_M ℓ χ Q`, with characters `χ_j` of absolute value
  `1` on `ker(H_M)`, trivial on the elements of `ker(H_M)` fixing `f`, and with values
  `χ_j(s(e_i))` eigenvalues of the translations by `s(e_i)` on `V_f`
  (`exists_exponentialPolynomial_of_finiteDimensional`); the finite-order hypothesis holds when
  `f` is invariant under an open subgroup and `ker(H_M)` is compact
  (`exists_pow_mul_eq_of_isCompact`, `exists_exponentialPolynomial_of_smooth`);
* if `f` has polynomial growth for a nonnegative subadditive size function `L` (the source's `σ`),
  the characters can be chosen unitary (`exists_unitary_exponentialPolynomial_of_hasPolynomialGrowth`),
  the direction (1) ⇒ (2) of the source in the form used later;
* the hypothesis on the differences of elements of `A^w(M)` used for the uniqueness in
  Lemma III.5.1 (`exists_unitary_exponentialPolynomial_sub`) and the resulting uniqueness
  (`eq_of_tendstoZeroAlongParabolic_of_mem`).

The lattice part is Renard's Appendix C.III in the Library,
`commutingTupleGeneralizedWeightPolynomialAssembly`.
-/

noncomputable section

open Filter Topology Asymptotics

namespace Langlands.HarishChandraSchwartz

open Langlands.IntegerLattice Langlands.HarmonicAnalysis.GroupAction

universe u

section Growth

variable {A : Type*}

/-- Polynomial growth for a size function `L`: `|φ(a)| ≤ C (1 + L(a))^r` for some `C` and
`r : ℕ`. For `L = σ` on `A_M` this is condition (1) of Waldspurger, I.2 (printed p. 242), for one
function. -/
def HasPolynomialGrowth (L : A → ℝ) (φ : A → ℂ) : Prop :=
  ∃ (C : ℝ) (r : ℕ), ∀ a, ‖φ a‖ ≤ C * (1 + L a) ^ r

variable {L : A → ℝ}

theorem hasPolynomialGrowth_zero : HasPolynomialGrowth L 0 :=
  ⟨0, 0, fun a => by simp⟩

theorem HasPolynomialGrowth.add (hL0 : ∀ a, 0 ≤ L a) {φ ψ : A → ℂ}
    (hφ : HasPolynomialGrowth L φ) (hψ : HasPolynomialGrowth L ψ) :
    HasPolynomialGrowth L (φ + ψ) := by
  obtain ⟨C₁, r₁, h₁⟩ := hφ
  obtain ⟨C₂, r₂, h₂⟩ := hψ
  refine ⟨|C₁| + |C₂|, max r₁ r₂, fun a => ?_⟩
  have h1 : 1 ≤ 1 + L a := by linarith [hL0 a]
  have h0 : ∀ r : ℕ, 0 ≤ (1 + L a) ^ r := fun r => pow_nonneg (by linarith) r
  have q₁ : C₁ * (1 + L a) ^ r₁ ≤ |C₁| * (1 + L a) ^ max r₁ r₂ :=
    (mul_le_mul_of_nonneg_right (le_abs_self C₁) (h0 r₁)).trans
      (mul_le_mul_of_nonneg_left (pow_le_pow_right₀ h1 (le_max_left _ _)) (abs_nonneg C₁))
  have q₂ : C₂ * (1 + L a) ^ r₂ ≤ |C₂| * (1 + L a) ^ max r₁ r₂ :=
    (mul_le_mul_of_nonneg_right (le_abs_self C₂) (h0 r₂)).trans
      (mul_le_mul_of_nonneg_left (pow_le_pow_right₀ h1 (le_max_right _ _)) (abs_nonneg C₂))
  calc ‖(φ + ψ) a‖ ≤ ‖φ a‖ + ‖ψ a‖ := norm_add_le _ _
    _ ≤ C₁ * (1 + L a) ^ r₁ + C₂ * (1 + L a) ^ r₂ := add_le_add (h₁ a) (h₂ a)
    _ ≤ |C₁| * (1 + L a) ^ max r₁ r₂ + |C₂| * (1 + L a) ^ max r₁ r₂ := add_le_add q₁ q₂
    _ = (|C₁| + |C₂|) * (1 + L a) ^ max r₁ r₂ := by ring

theorem HasPolynomialGrowth.smul {φ : A → ℂ} (hφ : HasPolynomialGrowth L φ) (c : ℂ) :
    HasPolynomialGrowth L (c • φ) := by
  obtain ⟨C, r, h⟩ := hφ
  refine ⟨‖c‖ * C, r, fun a => ?_⟩
  rw [Pi.smul_apply, smul_eq_mul, norm_mul, mul_assoc]
  exact mul_le_mul_of_nonneg_left (h a) (norm_nonneg c)

variable [Monoid A]

/-- Right translates of a function of polynomial growth have polynomial growth, for a
nonnegative subadditive `L`. -/
theorem HasPolynomialGrowth.comp_mul_right (hL0 : ∀ a, 0 ≤ L a)
    (hL : ∀ a b, L (a * b) ≤ L a + L b) {φ : A → ℂ} (hφ : HasPolynomialGrowth L φ) (x : A) :
    HasPolynomialGrowth L (fun a => φ (a * x)) := by
  obtain ⟨C, r, h⟩ := hφ
  refine ⟨|C| * (1 + L x) ^ r, r, fun a => ?_⟩
  have hle : 1 + L (a * x) ≤ (1 + L a) * (1 + L x) := by
    nlinarith [hL a x, hL0 a, hL0 x, hL0 (a * x), mul_nonneg (hL0 a) (hL0 x)]
  have hpow : (1 + L (a * x)) ^ r ≤ ((1 + L a) * (1 + L x)) ^ r :=
    pow_le_pow_left₀ (by linarith [hL0 (a * x)]) hle r
  calc ‖φ (a * x)‖ ≤ C * (1 + L (a * x)) ^ r := h _
    _ ≤ |C| * (1 + L (a * x)) ^ r :=
        mul_le_mul_of_nonneg_right (le_abs_self C) (pow_nonneg (by linarith [hL0 (a * x)]) r)
    _ ≤ |C| * ((1 + L a) * (1 + L x)) ^ r := mul_le_mul_of_nonneg_left hpow (abs_nonneg C)
    _ = |C| * (1 + L x) ^ r * (1 + L a) ^ r := by rw [mul_pow]; ring

/-- A real number whose powers grow at most polynomially is at most `1`. -/
theorem le_one_of_forall_pow_le {R D : ℝ} {r : ℕ}
    (h : ∀ k : ℕ, R ^ k ≤ D * (1 + (k : ℝ)) ^ r) : R ≤ 1 := by
  by_contra hR
  push Not at hR
  have hlo := isLittleO_pow_const_const_pow_of_one_lt (R := ℝ) r hR
  have hc : (0 : ℝ) < 1 / (2 ^ r * (|D| + 1)) := by positivity
  obtain ⟨N, hN⟩ := eventually_atTop.1 (hlo.bound hc)
  obtain ⟨k, hkN, hk1⟩ : ∃ k : ℕ, N ≤ k ∧ 1 ≤ k := ⟨max N 1, le_max_left _ _, le_max_right _ _⟩
  have hk1' : (1 : ℝ) ≤ k := by exact_mod_cast hk1
  have hRk : 0 < R ^ k := pow_pos (by linarith) k
  have hb := hN k hkN
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (by positivity),
    abs_of_pos hRk] at hb
  have h2 : (1 + (k : ℝ)) ^ r ≤ 2 ^ r * (k : ℝ) ^ r := by
    rw [← mul_pow]; exact pow_le_pow_left₀ (by positivity) (by linarith) r
  have key : R ^ k ≤ |D| * (2 ^ r * (1 / (2 ^ r * (|D| + 1)) * R ^ k)) :=
    calc R ^ k ≤ D * (1 + (k : ℝ)) ^ r := h k
      _ ≤ |D| * (1 + (k : ℝ)) ^ r := mul_le_mul_of_nonneg_right (le_abs_self D) (by positivity)
      _ ≤ |D| * (2 ^ r * (k : ℝ) ^ r) := mul_le_mul_of_nonneg_left h2 (abs_nonneg D)
      _ ≤ |D| * (2 ^ r * (1 / (2 ^ r * (|D| + 1)) * R ^ k)) := by gcongr
  have e : |D| * (2 ^ r * (1 / (2 ^ r * (|D| + 1)) * R ^ k)) = |D| / (|D| + 1) * R ^ k := by
    field_simp
  rw [e] at key
  have hlt : |D| / (|D| + 1) < 1 := by
    rw [div_lt_one (by positivity)]; linarith
  nlinarith

/-- An eigenvalue `z` of the right translation by `x` on a nonzero function of polynomial growth
has `|z| ≤ 1`. -/
theorem norm_le_one_of_hasPolynomialGrowth (hL0 : ∀ a, 0 ≤ L a)
    (hL : ∀ a b, L (a * b) ≤ L a + L b) {φ : A → ℂ} (hφ : HasPolynomialGrowth L φ)
    (hφ0 : φ ≠ 0) {x : A} {z : ℂ} (hz : ∀ a, φ (a * x) = z * φ a) : ‖z‖ ≤ 1 := by
  obtain ⟨C, r, h⟩ := hφ
  obtain ⟨b, hb⟩ : ∃ b, φ b ≠ 0 := by
    by_contra hcon
    push Not at hcon
    exact hφ0 (funext hcon)
  have hnb : 0 < ‖φ b‖ := norm_pos_iff.2 hb
  have hpow : ∀ k : ℕ, φ (b * x ^ k) = z ^ k * φ b := by
    intro k
    induction k with
    | zero => simp
    | succ k ih => rw [pow_succ, ← mul_assoc, hz, ih, pow_succ]; ring
  have hLpow : ∀ k : ℕ, L (b * x ^ k) ≤ L b + k * L x := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      rw [pow_succ, ← mul_assoc]
      have := hL (b * x ^ k) x
      push_cast
      linarith
  have hC : 0 ≤ C := by
    by_contra hneg
    push Not at hneg
    have h₁ := (norm_nonneg _).trans (h b)
    nlinarith [pow_pos (show (0 : ℝ) < 1 + L b by linarith [hL0 b]) r]
  refine le_one_of_forall_pow_le (D := C * (1 + L b + L x) ^ r / ‖φ b‖) (r := r) fun k => ?_
  have h1 : ‖z‖ ^ k * ‖φ b‖ ≤ C * (1 + L (b * x ^ k)) ^ r := by
    rw [← norm_pow, ← norm_mul, ← hpow]; exact h _
  have hk0 : (0 : ℝ) ≤ k := Nat.cast_nonneg k
  have h2 : 1 + L (b * x ^ k) ≤ (1 + L b + L x) * (1 + k) := by
    nlinarith [hLpow k, hL0 b, hL0 x, mul_nonneg hk0 (hL0 b), mul_nonneg hk0 (hL0 x)]
  have h3 : C * (1 + L (b * x ^ k)) ^ r ≤ C * ((1 + L b + L x) * (1 + k)) ^ r :=
    mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by linarith [hL0 (b * x ^ k)]) h2 r) hC
  rw [div_mul_eq_mul_div, le_div_iff₀ hnb]
  calc ‖z‖ ^ k * ‖φ b‖ ≤ C * ((1 + L b + L x) * (1 + k)) ^ r := h1.trans h3
    _ = C * (1 + L b + L x) ^ r * (1 + (k : ℝ)) ^ r := by rw [mul_pow]; ring

end Growth

section Translates

variable {A : Type u} [CommGroup A]

/-- The space `V_f` of Waldspurger, I.2 (printed p. 243): the span of the right translates
`a ↦ f(a x)` of `f`. The function `f` is `A`-finite when it is finite-dimensional. -/
def translateSpan (f : A → ℂ) : Submodule ℂ (A → ℂ) :=
  Submodule.span ℂ (Set.range fun x : A => rightFunctions x f)

theorem mem_translateSpan_self (f : A → ℂ) : f ∈ translateSpan f :=
  Submodule.subset_span ⟨1, by show rightFunctions 1 f = f; rw [map_one]; rfl⟩

theorem rightFunctions_mem_translateSpan {f : A → ℂ} (x : A) {φ : A → ℂ}
    (hφ : φ ∈ translateSpan f) : rightFunctions x φ ∈ translateSpan f := by
  induction hφ using Submodule.span_induction with
  | mem φ h =>
    obtain ⟨y, rfl⟩ := h
    exact Submodule.subset_span ⟨x * y, by
      show rightFunctions (x * y) f = _
      rw [map_mul]; rfl⟩
  | zero => rw [map_zero]; exact Submodule.zero_mem _
  | add φ ψ _ _ h₁ h₂ => rw [map_add]; exact Submodule.add_mem _ h₁ h₂
  | smul c φ _ h => rw [map_smul]; exact Submodule.smul_mem _ c h

/-- The right translation representation `ρ` of Waldspurger, I.2 on `V_f`. -/
def translateRep (f : A → ℂ) : Representation ℂ A (translateSpan f) :=
  (rightFunctions (G := A)).subrepresentation (translateSpan f)
    fun x _ hφ => rightFunctions_mem_translateSpan x hφ

theorem translateRep_apply (f : A → ℂ) (x : A) (φ : translateSpan f) (a : A) :
    (translateRep f x φ : A → ℂ) a = (φ : A → ℂ) (a * x) :=
  rightFunctions_apply x _ a

/-- Every element of `V_f` has polynomial growth if `f` has. -/
theorem hasPolynomialGrowth_of_mem_translateSpan {L : A → ℝ} (hL0 : ∀ a, 0 ≤ L a)
    (hL : ∀ a b, L (a * b) ≤ L a + L b) {f : A → ℂ} (hf : HasPolynomialGrowth L f)
    {φ : A → ℂ} (hφ : φ ∈ translateSpan f) : HasPolynomialGrowth L φ := by
  induction hφ using Submodule.span_induction with
  | mem φ h =>
    obtain ⟨y, rfl⟩ := h
    have e : rightFunctions y f = fun a => f (a * y) := funext fun a => rightFunctions_apply y f a
    show HasPolynomialGrowth L (rightFunctions y f)
    rw [e]
    exact hf.comp_mul_right hL0 hL y
  | zero => exact hasPolynomialGrowth_zero
  | add φ ψ _ _ h₁ h₂ => exact h₁.add hL0 h₂
  | smul c φ _ h => exact h.smul c

end Translates

section Expansion

variable {A : Type u} [CommGroup A] {E : Type*} [AddCommGroup E] [Module ℝ E]

/-- Invariance of `f` under the right translation by `x` passes to every element of `V_f`. -/
theorem apply_mul_eq_of_mem_translateSpan {f : A → ℂ} {x : A} (hx : ∀ a, f (a * x) = f a)
    {φ : A → ℂ} (hφ : φ ∈ translateSpan f) : ∀ a, φ (a * x) = φ a := by
  induction hφ using Submodule.span_induction with
  | mem φ h =>
    obtain ⟨y, rfl⟩ := h
    intro a
    show rightFunctions y f (a * x) = rightFunctions y f a
    rw [rightFunctions_apply, rightFunctions_apply, mul_right_comm, hx]
  | zero => intro a; rfl
  | add φ ψ _ _ h₁ h₂ => intro a; simp only [Pi.add_apply, h₁, h₂]
  | smul c φ _ h => intro a; simp only [Pi.smul_apply, h]

/-- The lattice coordinates: if `ℓ_i(H_M(s(n))) = n_i` and every `a` lies in `ker(H_M) · s(ℤ^d)`,
then `a ↦ n(a)`, with `ℓ_i(H_M(a)) = n(a)_i` and `H_M(a / s(n(a))) = 0`, is a homomorphism. -/
theorem exists_latticeCoordinate {HM : A → E} (hHM : ∀ a b, HM (a * b) = HM a + HM b) {d : ℕ}
    (s : Lattice d →* A) (ℓ : Fin d → Module.Dual ℝ E)
    (hs : ∀ n i, ℓ i (HM (s n)) = (n.toAdd i : ℝ)) (hA : ∀ a, ∃ n, HM (a * (s n)⁻¹) = 0) :
    ∃ nH : A →* Lattice d, ∀ a, (∀ i, ((nH a).toAdd i : ℝ) = ℓ i (HM a)) ∧
      HM (a / s (nH a)) = 0 := by
  choose nA hnA using hA
  have key : ∀ a i, ((nA a).toAdd i : ℝ) = ℓ i (HM a) := by
    intro a i
    have e : HM a = HM (a * (s (nA a))⁻¹) + HM (s (nA a)) := by
      rw [← hHM, inv_mul_cancel_right]
    rw [e, hnA a, zero_add, hs]
  have h1 : HM 1 = 0 := by simpa using hHM 1 1
  refine ⟨{ toFun := nA, map_one' := ?_, map_mul' := ?_ }, fun a => ⟨key a, ?_⟩⟩
  · apply Multiplicative.toAdd.injective
    funext i
    have := key 1 i
    rw [h1, map_zero] at this
    rw [toAdd_one, Pi.zero_apply]
    exact_mod_cast this
  · intro a b
    apply Multiplicative.toAdd.injective
    funext i
    have := key (a * b) i
    rw [hHM, map_add, ← key a, ← key b] at this
    rw [toAdd_mul, Pi.add_apply]
    exact_mod_cast this
  · show HM (a / s (nA a)) = 0
    rw [div_eq_mul_inv]
    exact hnA a

variable {ι κ κ' : Type*} [Fintype κ] [Fintype κ']

/-- Reindexing an exponential polynomial along an equivalence of index types. -/
theorem exponentialPolynomial_comp_equiv (HM : A → E) (ℓ : ι → Module.Dual ℝ E) (e : κ' ≃ κ)
    (χ : κ → A →* ℂˣ) (Q : κ → MvPolynomial ι ℂ) :
    exponentialPolynomial HM ℓ (fun j => χ (e j)) (fun j => Q (e j)) =
      exponentialPolynomial HM ℓ χ Q :=
  funext fun a => Equiv.sum_comp e
    (fun k => (χ k a : ℂ) * MvPolynomial.eval (fun i => ((ℓ i (HM a) : ℝ) : ℂ)) (Q k))

/-- The sum of two exponential polynomials, indexed by `Fin.append`. -/
theorem exponentialPolynomial_append (HM : A → E) (ℓ : ι → Module.Dual ℝ E) {n₁ n₂ : ℕ}
    (χ₁ : Fin n₁ → A →* ℂˣ) (χ₂ : Fin n₂ → A →* ℂˣ) (Q₁ : Fin n₁ → MvPolynomial ι ℂ)
    (Q₂ : Fin n₂ → MvPolynomial ι ℂ) (a : A) :
    exponentialPolynomial HM ℓ (Fin.append χ₁ χ₂) (Fin.append Q₁ Q₂) a =
      exponentialPolynomial HM ℓ χ₁ Q₁ a + exponentialPolynomial HM ℓ χ₂ Q₂ a := by
  simp only [exponentialPolynomial, Fin.sum_univ_add, Fin.append_left, Fin.append_right]

/-- Negating the polynomials negates the exponential polynomial. -/
theorem exponentialPolynomial_neg (HM : A → E) (ℓ : ι → Module.Dual ℝ E) (χ : κ → A →* ℂˣ)
    (Q : κ → MvPolynomial ι ℂ) (a : A) :
    exponentialPolynomial HM ℓ χ (fun j => -Q j) a = -exponentialPolynomial HM ℓ χ Q a := by
  simp only [exponentialPolynomial, map_neg, mul_neg, Finset.sum_neg_distrib]

/-- **Waldspurger, I.2** (printed pp. 242–243), expansion of an `A_M`-finite function. Let
`H_M : A → E` be additive, `s : ℤ^d → A` a homomorphism and `ℓ_i` linear forms on `E` with
`ℓ_i(H_M(s(n))) = n_i` and `A = ker(H_M) · s(ℤ^d)`, and let `f : A → ℂ` have a finite-dimensional
space of right translates `V_f` and be invariant under the right translation by some power `c^N`,
`N > 0`, of each `c ∈ ker(H_M)`. Then `f(a) = ∑_j χ_j(a) Q_j(ℓ(H_M(a)))` for finitely many
characters `χ_j` with `|χ_j| = 1` on `ker(H_M)` and `χ_j(c) = 1` for every `c ∈ ker(H_M)` under
whose right translation `f` is invariant, and each value `χ_j(s(e_i))` is an eigenvalue of the
right translation by `s(e_i)` on a nonzero element of `V_f`. -/
theorem exists_exponentialPolynomial_of_finiteDimensional {HM : A → E}
    (hHM : ∀ a b, HM (a * b) = HM a + HM b) {d : ℕ} (s : Lattice d →* A)
    (ℓ : Fin d → Module.Dual ℝ E) (hs : ∀ n i, ℓ i (HM (s n)) = (n.toAdd i : ℝ))
    (hA : ∀ a, ∃ n, HM (a * (s n)⁻¹) = 0) {f : A → ℂ}
    (hf : FiniteDimensional ℂ (translateSpan f))
    (hfin : ∀ c, HM c = 0 → ∃ N : ℕ, 0 < N ∧ ∀ a, f (a * c ^ N) = f a) :
    ∃ (n : ℕ) (χ : Fin n → A →* ℂˣ) (Q : Fin n → MvPolynomial (Fin d) ℂ),
      (∀ j, (∀ c, HM c = 0 → ‖(χ j c : ℂ)‖ = 1) ∧
        (∀ c, HM c = 0 → (∀ a, f (a * c) = f a) → χ j c = 1) ∧
        ∀ i, ∃ φ ∈ translateSpan f, φ ≠ 0 ∧
          ∀ a, φ (a * s (generator d i)) = χ j (s (generator d i)) * φ a) ∧
      ∀ a, f a = exponentialPolynomial HM ℓ χ Q a := by
  classical
  have := hf
  obtain ⟨nH, hnH⟩ := exists_latticeCoordinate hHM s ℓ hs hA
  obtain ⟨cH, hcH⟩ : ∃ cH : A →* A, ∀ a, cH a = a / s (nH a) :=
    ⟨MonoidHom.id A / s.comp nH, fun a => rfl⟩
  have hker : ∀ a, HM (cH a) = 0 := fun a => by rw [hcH]; exact (hnH a).2
  have hnH_ker : ∀ c, HM c = 0 → nH c = 1 := by
    intro c hc
    apply Multiplicative.toAdd.injective
    funext i
    have := (hnH c).1 i
    rw [hc, map_zero] at this
    rw [toAdd_one, Pi.zero_apply]
    exact_mod_cast this
  have hnH_s : ∀ m, nH (s m) = m := by
    intro m
    apply Multiplicative.toAdd.injective
    funext i
    have := (hnH (s m)).1 i
    rw [hs] at this
    exact_mod_cast this
  have hcH_ker : ∀ c, HM c = 0 → cH c = c := by
    intro c hc
    rw [hcH, hnH_ker c hc, map_one, div_one]
  have hcH_s : ∀ m, cH (s m) = 1 := by
    intro m
    rw [hcH, hnH_s, div_self']
  -- the elements of `ker(H_M)` act on `V_f` with finite order
  have hord : ∀ c, HM c = 0 → ∃ N : ℕ, 0 < N ∧ translateRep f c ^ N = 1 := by
    intro c hc
    obtain ⟨N, hN, hNf⟩ := hfin c hc
    refine ⟨N, hN, ?_⟩
    rw [← map_pow]
    apply LinearMap.ext
    intro φ
    apply Subtype.ext
    funext a
    rw [translateRep_apply, Module.End.one_apply]
    exact apply_mul_eq_of_mem_translateSpan hNf φ.2 a
  have hss : ∀ a, Module.End.IsFinitelySemisimple (translateRep f (cH a)) := by
    intro a
    obtain ⟨N, hN, hTN⟩ := hord (cH a) (hker a)
    apply Module.End.IsSemisimple.isFinitelySemisimple
    apply Module.End.isSemisimple_of_squarefree_aeval_eq_zero
      (Polynomial.separable_X_pow_sub_C (1 : ℂ) (by exact_mod_cast hN.ne')
        one_ne_zero).squarefree
    rw [map_sub, Polynomial.aeval_X_pow, Polynomial.aeval_C, map_one, hTN, sub_self]
  -- joint eigenspace decomposition of `V_f` for the translations by `ker(H_M)`
  have hcomm : Pairwise fun a b : A =>
      Commute (translateRep f (cH a)) (translateRep f (cH b)) :=
    fun a b _ => (Commute.all (cH a) (cH b)).map (translateRep f)
  have htop := Module.End.iSup_iInf_maxGenEigenspace_eq_top_of_iSup_maxGenEigenspace_eq_top_of_commute
    (fun a => translateRep f (cH a)) hcomm (fun a => Module.End.iSup_maxGenEigenspace_eq_top _)
  obtain ⟨F, hF, hFsum⟩ := (Submodule.mem_iSup_iff_exists_finsupp _
    (⟨f, mem_translateSpan_self f⟩ : translateSpan f)).1 (by rw [htop]; exact Submodule.mem_top)
  have hFeig : ∀ χ a, translateRep f (cH a) (F χ) = χ a • F χ := by
    intro χ a
    have h1 := (Submodule.mem_iInf _).1 (hF χ) a
    rw [(hss a).maxGenEigenspace_eq_eigenspace] at h1
    exact Module.End.mem_eigenspace_iff.1 h1
  have hFne : ∀ χ ∈ F.support, F χ ≠ 0 := fun χ hχ => Finsupp.mem_support_iff.1 hχ
  have hchar : ∀ χ ∈ F.support, ∃ X : A →* ℂˣ, ∀ a, (X a : ℂ) = χ a := by
    intro χ hχ
    have inj := smul_left_injective ℂ (hFne χ hχ)
    have hmul : ∀ a b, χ (a * b) = χ a * χ b := by
      intro a b
      apply inj
      show χ (a * b) • F χ = (χ a * χ b) • F χ
      rw [← hFeig χ (a * b), map_mul, map_mul, Module.End.mul_apply, hFeig χ b, map_smul,
        hFeig χ a, smul_smul, mul_comm]
    have hone : χ 1 = 1 := by
      apply inj
      show χ 1 • F χ = (1 : ℂ) • F χ
      rw [← hFeig χ 1, map_one, map_one, one_smul, Module.End.one_apply]
    exact ⟨(MonoidHom.mk ⟨χ, hone⟩ hmul).toHomUnits, fun a => rfl⟩
  choose! X hX using hchar
  have hunit : ∀ χ ∈ F.support, ∀ c, HM c = 0 → ‖χ c‖ = 1 := by
    intro χ hχ c hc
    obtain ⟨N, hN, hTN⟩ := hord c hc
    have h1 := hFeig χ c
    rw [hcH_ker c hc] at h1
    have hv : (translateRep f c ^ N) (F χ) = χ c ^ N • F χ :=
      Module.End.HasEigenvector.pow_apply ⟨Module.End.mem_eigenspace_iff.2 h1, hFne χ hχ⟩ N
    rw [hTN, Module.End.one_apply] at hv
    have hpow : χ c ^ N = 1 := by
      apply smul_left_injective ℂ (hFne χ hχ)
      show χ c ^ N • F χ = (1 : ℂ) • F χ
      rw [one_smul]
      exact hv.symm
    exact Complex.norm_eq_one_of_pow_eq_one hpow hN.ne'
  have hlat1 : ∀ χ ∈ F.support, ∀ m, χ (s m) = 1 := by
    intro χ hχ m
    apply smul_left_injective ℂ (hFne χ hχ)
    show χ (s m) • F χ = (1 : ℂ) • F χ
    rw [← hFeig χ (s m), hcH_s, map_one, one_smul, Module.End.one_apply]
  -- the lattice part (Renard, Appendix C.III)
  obtain ⟨u, hu0⟩ : ∃ u, u = (tupleRepresentationEquiv d (translateSpan f)).symm
      ((translateRep f).comp s) := ⟨_, rfl⟩
  have hu : ∀ m, tupleRepresentationEquiv d (translateSpan f) u m = translateRep f (s m) := by
    intro m
    rw [hu0, tupleRepresentationEquiv_right_inv]
    rfl
  have hu1 : ∀ i, ((u.1 i : (Module.End ℂ (translateSpan f))ˣ) : Module.End ℂ (translateSpan f)) =
      translateRep f (s (generator d i)) := by
    intro i
    rw [hu0, tupleRepresentationEquiv_symm_apply_coe]
    rfl
  obtain ⟨b, B, S, -, hS, hcoeff⟩ :=
    commutingTupleGeneralizedWeightPolynomialAssembly d (translateSpan f) u
  let ev : translateSpan f →ₗ[ℂ] ℂ :=
    (LinearMap.proj (R := ℂ) (φ := fun _ : A => ℂ) 1).comp (translateSpan f).subtype
  have hval : ∀ χ a, (F χ : A → ℂ) a = χ a * ∑ w ∈ S, (coordinateCharacter w (nH a) : ℂ) *
      MvPolynomial.eval (fun t => ((ℓ t (HM a) : ℝ) : ℂ))
        (generalizedWeightCoefficientPolynomial u w (b w) B (F χ) ev) := by
    intro χ a
    have e1 : (F χ : A → ℂ) a =
        ev (tupleRepresentationEquiv d (translateSpan f) u (nH a) (translateRep f (cH a) (F χ))) := by
      rw [hu]
      show (F χ : A → ℂ) a =
        ((translateRep f (s (nH a)) (translateRep f (cH a) (F χ)) : A → ℂ) 1)
      rw [translateRep_apply, translateRep_apply, one_mul, hcH, mul_comm, div_mul_cancel]
    rw [e1, hFeig, map_smul, map_smul, smul_eq_mul, hcoeff]
    have ht : (fun t => (((nH a).toAdd t : ℤ) : ℂ)) = fun t => ((ℓ t (HM a) : ℝ) : ℂ) := by
      funext t
      rw [← (hnH a).1 t, Complex.ofReal_intCast]
    rw [ht]
  have hfa : ∀ a, f a = ∑ χ ∈ F.support, (F χ : A → ℂ) a := by
    intro a
    have := congrArg (fun v : translateSpan f => (v : A → ℂ) a) hFsum
    simp only [Finsupp.sum, Submodule.coe_sum, Finset.sum_apply] at this
    exact this.symm
  -- the characters `χ · (w ∘ n)` indexed by the pairs `(χ, w)`
  let Ψ : ↥(F.support ×ˢ S) → A →* ℂˣ :=
    fun p => X p.1.1 * (coordinateCharacter p.1.2).comp nH
  let P : ↥(F.support ×ˢ S) → MvPolynomial (Fin d) ℂ :=
    fun p => generalizedWeightCoefficientPolynomial u p.1.2 (b p.1.2) B (F p.1.1) ev
  have hΨ : ∀ p : ↥(F.support ×ˢ S), (∀ c, HM c = 0 → ‖(Ψ p c : ℂ)‖ = 1) ∧
      (∀ c, HM c = 0 → (∀ a, f (a * c) = f a) → Ψ p c = 1) ∧
      ∀ i, ∃ φ ∈ translateSpan f, φ ≠ 0 ∧
        ∀ a, φ (a * s (generator d i)) = Ψ p (s (generator d i)) * φ a := by
    intro p
    obtain ⟨hp1, hp2⟩ := Finset.mem_product.1 p.2
    refine ⟨fun c hc => ?_, fun c hc hfc => ?_, fun i => ?_⟩
    · simp only [Ψ, MonoidHom.mul_apply, MonoidHom.comp_apply, hX _ hp1, hnH_ker c hc, map_one,
        mul_one]
      exact hunit _ hp1 c hc
    · apply Units.ext
      simp only [Ψ, MonoidHom.mul_apply, MonoidHom.comp_apply, hnH_ker c hc, map_one, mul_one,
        hX _ hp1, Units.val_one]
      apply smul_left_injective ℂ (hFne _ hp1)
      show p.1.1 c • F p.1.1 = (1 : ℂ) • F p.1.1
      rw [← hFeig _ c, hcH_ker c hc, one_smul]
      apply Subtype.ext
      funext a
      rw [translateRep_apply]
      exact apply_mul_eq_of_mem_translateSpan hfc (F p.1.1).2 a
    · obtain ⟨v, hv, hv0⟩ := Submodule.ne_bot_iff _ |>.1 ((hS _).1 hp2)
      have hmax : (u.1 i : Module.End ℂ (translateSpan f)).maxGenEigenspace (p.1.2 i : ℂ) ≠ ⊥ :=
        Submodule.ne_bot_iff _ |>.2 ⟨v, mem_generalizedWeightBlock.1 hv i, hv0⟩
      have hev : (u.1 i : Module.End ℂ (translateSpan f)).HasEigenvalue (p.1.2 i : ℂ) :=
        Module.End.HasUnifEigenvalue.lt zero_lt_one hmax
      obtain ⟨φ, hφ⟩ := hev.exists_hasEigenvector
      have hφ1 := Module.End.mem_eigenspace_iff.1 hφ.1
      rw [hu1] at hφ1
      refine ⟨φ, φ.2, fun h => hφ.2 (Submodule.coe_eq_zero.1 h), fun a => ?_⟩
      have hval' : Ψ p (s (generator d i)) = p.1.2 i := by
        apply Units.ext
        simp only [Ψ, MonoidHom.mul_apply, MonoidHom.comp_apply, Units.val_mul, hX _ hp1,
          hlat1 _ hp1, hnH_s, coordinateCharacter_generator, one_mul]
      rw [hval', ← translateRep_apply, hφ1]
      rfl
  have hexp : ∀ a, f a = exponentialPolynomial HM ℓ Ψ P a := by
    intro a
    rw [hfa a]
    refine Eq.trans ?_ (Finset.sum_coe_sort (F.support ×ˢ S) (fun q =>
      ((X q.1 * (coordinateCharacter q.2).comp nH) a : ℂ) *
        MvPolynomial.eval (fun t => ((ℓ t (HM a) : ℝ) : ℂ))
          (generalizedWeightCoefficientPolynomial u q.2 (b q.2) B (F q.1) ev))).symm
    rw [Finset.sum_product]
    refine Finset.sum_congr rfl fun χ hχ => ?_
    rw [hval, Finset.mul_sum]
    refine Finset.sum_congr rfl fun w _ => ?_
    rw [MonoidHom.mul_apply, MonoidHom.comp_apply, Units.val_mul, hX χ hχ, mul_assoc]
  let e := (Fintype.equivFin ↥(F.support ×ˢ S)).symm
  refine ⟨Fintype.card ↥(F.support ×ˢ S), fun j => Ψ (e j), fun j => P (e j),
    fun j => hΨ (e j), fun a => ?_⟩
  rw [exponentialPolynomial_comp_equiv HM ℓ e Ψ P]
  exact hexp a

/-- **Waldspurger, I.2** (printed pp. 242–243), the direction (1) ⇒ (2): under the hypotheses
of `exists_exponentialPolynomial_of_finiteDimensional`, if moreover `|f(a)| ≤ C (1 + L(a))^r`
for a nonnegative subadditive `L` (the source's `σ`), then `f` is an exponential polynomial
with unitary characters. -/
theorem exists_unitary_exponentialPolynomial_of_hasPolynomialGrowth {HM : A → E}
    (hHM : ∀ a b, HM (a * b) = HM a + HM b) {d : ℕ} (s : Lattice d →* A)
    (ℓ : Fin d → Module.Dual ℝ E) (hs : ∀ n i, ℓ i (HM (s n)) = (n.toAdd i : ℝ))
    (hA : ∀ a, ∃ n, HM (a * (s n)⁻¹) = 0) {L : A → ℝ} (hL0 : ∀ a, 0 ≤ L a)
    (hL : ∀ a b, L (a * b) ≤ L a + L b) {f : A → ℂ}
    (hf : FiniteDimensional ℂ (translateSpan f))
    (hfin : ∀ c, HM c = 0 → ∃ N : ℕ, 0 < N ∧ ∀ a, f (a * c ^ N) = f a)
    (hgr : HasPolynomialGrowth L f) :
    ∃ (n : ℕ) (χ : Fin n → A →* ℂˣ) (Q : Fin n → MvPolynomial (Fin d) ℂ),
      (∀ j a, ‖(χ j a : ℂ)‖ = 1) ∧ ∀ a, f a = exponentialPolynomial HM ℓ χ Q a := by
  obtain ⟨n, χ, Q, hχ, hexp⟩ :=
    exists_exponentialPolynomial_of_finiteDimensional hHM s ℓ hs hA hf hfin
  refine ⟨n, χ, Q, fun j a => ?_, hexp⟩
  obtain ⟨hker, -, heig⟩ := hχ j
  have hgen : ∀ i, ‖(χ j (s (generator d i)) : ℂ)‖ = 1 := by
    intro i
    obtain ⟨φ, hφV, hφ0, hφ⟩ := heig i
    have hgφ := hasPolynomialGrowth_of_mem_translateSpan hL0 hL hgr hφV
    have h1 := norm_le_one_of_hasPolynomialGrowth hL0 hL hgφ hφ0 hφ
    have hinv : ∀ a, φ (a * (s (generator d i))⁻¹) =
        (((χ j (s (generator d i)))⁻¹ : ℂˣ) : ℂ) * φ a := by
      intro a
      have h := hφ (a * (s (generator d i))⁻¹)
      rw [inv_mul_cancel_right] at h
      rw [h, ← mul_assoc, Units.inv_mul, one_mul]
    have h2 := norm_le_one_of_hasPolynomialGrowth hL0 hL hgφ hφ0 hinv
    rw [Units.val_inv_eq_inv_val, norm_inv,
      inv_le_one₀ (norm_pos_iff.2 (χ j (s (generator d i))).ne_zero)] at h2
    exact le_antisymm h1 h2
  obtain ⟨m, hm⟩ := hA a
  have hlat : ‖(χ j (s m) : ℂ)‖ = 1 := by
    rw [← MonoidHom.comp_apply, ← coordinateCharacter_reconstruction ((χ j).comp s),
      coe_coordinateCharacter, norm_prod]
    exact Finset.prod_eq_one fun i _ => by
      rw [norm_zpow, MonoidHom.comp_apply, hgen i, one_zpow]
  have e : χ j a = χ j (a * (s m)⁻¹) * χ j (s m) := by
    rw [← map_mul, inv_mul_cancel_right]
  rw [e, Units.val_mul, norm_mul, hker _ hm, hlat, one_mul]

/-- An element of a compact subgroup `K` of a topological group has a positive power in a given
open subgroup `U`, since `K / (U ∩ K)` is finite. -/
theorem exists_pow_mem_of_isCompact [TopologicalSpace A] [IsTopologicalGroup A] {K U : Subgroup A}
    (hK : IsCompact (K : Set A)) (hU : IsOpen (U : Set A)) {c : A} (hc : c ∈ K) :
    ∃ N : ℕ, 0 < N ∧ c ^ N ∈ U := by
  have : CompactSpace K := isCompact_iff_compactSpace.1 hK
  have : Finite (K ⧸ U.subgroupOf K) :=
    Subgroup.quotient_finite_of_isOpen _ (Subgroup.subgroupOf_isOpen K U hU)
  obtain ⟨N, hN, -, hmem⟩ := Subgroup.exists_pow_mem_of_relIndex_ne_zero
    (Subgroup.index_ne_zero_of_finite (H := U.subgroupOf K)) hc
  exact ⟨N, hN, (Subgroup.mem_inf.1 hmem).1⟩

omit [Module ℝ E] in
/-- The hypothesis `hfin` of `exists_exponentialPolynomial_of_finiteDimensional` for a smooth
function: if `f` is invariant under the right translations by an open subgroup `U` and
`ker(H_M)` is compact (the source's `A_M^1`), then `f` is invariant under the right translation
by a positive power of each `c ∈ ker(H_M)`. -/
theorem exists_pow_mul_eq_of_isCompact [TopologicalSpace A] [IsTopologicalGroup A] {HM : A → E}
    (hHM : ∀ a b, HM (a * b) = HM a + HM b) (hcpt : IsCompact {c : A | HM c = 0})
    {U : Subgroup A} (hU : IsOpen (U : Set A)) {f : A → ℂ}
    (hfU : ∀ u ∈ U, ∀ a, f (a * u) = f a) (c : A) (hc : HM c = 0) :
    ∃ N : ℕ, 0 < N ∧ ∀ a, f (a * c ^ N) = f a := by
  have h1 : HM 1 = 0 := by simpa using hHM 1 1
  let K : Subgroup A :=
    { carrier := {c | HM c = 0}
      mul_mem' := fun {a b} ha hb => by
        show HM (a * b) = 0
        rw [hHM, show HM a = 0 from ha, show HM b = 0 from hb, add_zero]
      one_mem' := h1
      inv_mem' := fun {a} ha => by
        show HM a⁻¹ = 0
        have e := hHM a⁻¹ a
        rw [inv_mul_cancel, h1, show HM a = 0 from ha, add_zero] at e
        exact e.symm }
  obtain ⟨N, hN, hNU⟩ := exists_pow_mem_of_isCompact (K := K) hcpt hU (show HM c = 0 from hc)
  exact ⟨N, hN, fun a => hfU _ hNU a⟩

/-- **Waldspurger, I.2** (printed pp. 242–243) for a smooth `A_M`-finite function: if `f` is
invariant under the right translations by an open subgroup `U`, `ker(H_M)` is compact and `V_f` is
finite-dimensional, then `f(a) = ∑_j χ_j(a) Q_j(ℓ(H_M(a)))` with characters `χ_j` that have
`|χ_j| = 1` on `ker(H_M)` and are trivial on `U ∩ ker(H_M)`, and each value `χ_j(s(e_i))` is an
eigenvalue of the right translation by `s(e_i)` on a nonzero element of `V_f`. -/
theorem exists_exponentialPolynomial_of_smooth [TopologicalSpace A] [IsTopologicalGroup A]
    {HM : A → E} (hHM : ∀ a b, HM (a * b) = HM a + HM b) {d : ℕ} (s : Lattice d →* A)
    (ℓ : Fin d → Module.Dual ℝ E) (hs : ∀ n i, ℓ i (HM (s n)) = (n.toAdd i : ℝ))
    (hA : ∀ a, ∃ n, HM (a * (s n)⁻¹) = 0) (hcpt : IsCompact {c : A | HM c = 0})
    {U : Subgroup A} (hU : IsOpen (U : Set A)) {f : A → ℂ}
    (hfU : ∀ u ∈ U, ∀ a, f (a * u) = f a) (hf : FiniteDimensional ℂ (translateSpan f)) :
    ∃ (n : ℕ) (χ : Fin n → A →* ℂˣ) (Q : Fin n → MvPolynomial (Fin d) ℂ),
      (∀ j, (∀ c, HM c = 0 → ‖(χ j c : ℂ)‖ = 1) ∧ (∀ u ∈ U, HM u = 0 → χ j u = 1) ∧
        ∀ i, ∃ φ ∈ translateSpan f, φ ≠ 0 ∧
          ∀ a, φ (a * s (generator d i)) = χ j (s (generator d i)) * φ a) ∧
      ∀ a, f a = exponentialPolynomial HM ℓ χ Q a := by
  obtain ⟨n, χ, Q, hχ, hexp⟩ := exists_exponentialPolynomial_of_finiteDimensional hHM s ℓ hs hA hf
    (exists_pow_mul_eq_of_isCompact hHM hcpt hU hfU)
  exact ⟨n, χ, Q, fun j => ⟨(hχ j).1, fun u hu hu0 => (hχ j).2.1 u hu0 (hfU u hu), (hχ j).2.2⟩,
    hexp⟩

/-- The hypothesis on differences used for the uniqueness in Waldspurger, Lemma III.5.1
(printed p. 270), for functions `g` on a monoid `M` containing `A` through `j`: if each `g ∈ C`
lies in a finite-dimensional space of functions stable under the right translations by `j(A)`, is
invariant under the right translation by `j(c^N)` for some `N > 0` and each `c ∈ ker(H_M)`, and
`a ↦ g(m j(a))` has polynomial growth for every `m`, then each `a ↦ g₁(m j(a)) - g₂(m j(a))` is an
exponential polynomial with unitary characters. -/
theorem exists_unitary_exponentialPolynomial_sub {M : Type*} [Monoid M] (j : A →* M)
    {HM : A → E} (hHM : ∀ a b, HM (a * b) = HM a + HM b) {d : ℕ} (s : Lattice d →* A)
    (ℓ : Fin d → Module.Dual ℝ E) (hs : ∀ n i, ℓ i (HM (s n)) = (n.toAdd i : ℝ))
    (hA : ∀ a, ∃ n, HM (a * (s n)⁻¹) = 0) {L : A → ℝ} (hL0 : ∀ a, 0 ≤ L a)
    (hL : ∀ a b, L (a * b) ≤ L a + L b) {C : Set (M → ℂ)}
    (hCfin : ∀ g ∈ C, ∃ W : Submodule ℂ (M → ℂ), FiniteDimensional ℂ W ∧ g ∈ W ∧
      ∀ x : A, ∀ w ∈ W, (fun y => w (y * j x)) ∈ W)
    (hCinv : ∀ g ∈ C, ∀ c, HM c = 0 → ∃ N : ℕ, 0 < N ∧ ∀ y, g (y * j (c ^ N)) = g y)
    (hCgr : ∀ g ∈ C, ∀ m, HasPolynomialGrowth L (fun a => g (m * j a))) :
    ∀ g₁ ∈ C, ∀ g₂ ∈ C, ∀ m, ∃ (n : ℕ) (χ : Fin n → A →* ℂˣ)
      (Q : Fin n → MvPolynomial (Fin d) ℂ), (∀ i a, ‖(χ i a : ℂ)‖ = 1) ∧
        ∀ a, g₁ (m * j a) - g₂ (m * j a) = exponentialPolynomial HM ℓ χ Q a := by
  have one : ∀ g ∈ C, ∀ m, ∃ (n : ℕ) (χ : Fin n → A →* ℂˣ)
      (Q : Fin n → MvPolynomial (Fin d) ℂ), (∀ i a, ‖(χ i a : ℂ)‖ = 1) ∧
        ∀ a, g (m * j a) = exponentialPolynomial HM ℓ χ Q a := by
    intro g hg m
    obtain ⟨W, hW, hgW, hWst⟩ := hCfin g hg
    have hle : translateSpan (fun a => g (m * j a)) ≤
        W.map (LinearMap.funLeft ℂ ℂ (fun a : A => m * j a)) := by
      refine Submodule.span_le.2 ?_
      rintro _ ⟨x, rfl⟩
      refine ⟨fun y => g (y * j x), hWst x g hgW, ?_⟩
      funext a
      show g (m * j a * j x) = rightFunctions x (fun a => g (m * j a)) a
      rw [rightFunctions_apply, map_mul, mul_assoc]
    have := hW
    have hfd : FiniteDimensional ℂ (translateSpan (fun a => g (m * j a))) :=
      Submodule.finiteDimensional_of_le hle
    refine exists_unitary_exponentialPolynomial_of_hasPolynomialGrowth hHM s ℓ hs hA hL0 hL
      hfd (fun c hc => ?_) (hCgr g hg m)
    obtain ⟨N, hN, hNg⟩ := hCinv g hg c hc
    exact ⟨N, hN, fun a => by rw [map_mul, ← mul_assoc, hNg]⟩
  intro g₁ hg₁ g₂ hg₂ m
  obtain ⟨n₁, χ₁, Q₁, hχ₁, h₁⟩ := one g₁ hg₁ m
  obtain ⟨n₂, χ₂, Q₂, hχ₂, h₂⟩ := one g₂ hg₂ m
  refine ⟨n₁ + n₂, Fin.append χ₁ χ₂, Fin.append Q₁ (fun i => -Q₂ i), fun i a => ?_, fun a => ?_⟩
  · refine Fin.addCases (fun i => ?_) (fun i => ?_) i
    · rw [Fin.append_left]; exact hχ₁ i a
    · rw [Fin.append_right]; exact hχ₂ i a
  · rw [exponentialPolynomial_append, exponentialPolynomial_neg, h₁, h₂, sub_eq_add_neg]

/-- Uniqueness in Waldspurger, Lemma III.5.1 (printed p. 270), for functions of the class `C` of
`exists_unitary_exponentialPolynomial_sub`: if `f₁, f₂ ∈ C` both satisfy
`lim_{a →_P ∞} [F(m j(a)) - f_i(m j(a))] = 0` for every `m`, then `f₁ = f₂`. -/
theorem eq_of_tendstoZeroAlongParabolic_of_mem {M : Type*} [Monoid M] (j : A →* M) {HM : A → E}
    (hHM : ∀ a b, HM (a * b) = HM a + HM b) {S : Finset (Module.Dual ℝ E)} {a₀ : A}
    (ha₀ : ∀ α ∈ S, 0 < α (HM a₀)) {d : ℕ} (s : Lattice d →* A)
    (ℓ : Fin d → Module.Dual ℝ E) (hs : ∀ n i, ℓ i (HM (s n)) = (n.toAdd i : ℝ))
    (hA : ∀ a, ∃ n, HM (a * (s n)⁻¹) = 0) {L : A → ℝ} (hL0 : ∀ a, 0 ≤ L a)
    (hL : ∀ a b, L (a * b) ≤ L a + L b) {C : Set (M → ℂ)}
    (hCfin : ∀ g ∈ C, ∃ W : Submodule ℂ (M → ℂ), FiniteDimensional ℂ W ∧ g ∈ W ∧
      ∀ x : A, ∀ w ∈ W, (fun y => w (y * j x)) ∈ W)
    (hCinv : ∀ g ∈ C, ∀ c, HM c = 0 → ∃ N : ℕ, 0 < N ∧ ∀ y, g (y * j (c ^ N)) = g y)
    (hCgr : ∀ g ∈ C, ∀ m, HasPolynomialGrowth L (fun a => g (m * j a))) {F f₁ f₂ : M → ℂ}
    (hf₁ : f₁ ∈ C) (hf₂ : f₂ ∈ C)
    (h₁ : ∀ m, TendstoZeroAlongParabolic HM S (fun a => F (m * j a) - f₁ (m * j a)))
    (h₂ : ∀ m, TendstoZeroAlongParabolic HM S (fun a => F (m * j a) - f₂ (m * j a))) :
    f₁ = f₂ :=
  eq_of_tendstoZeroAlongParabolic j hHM ha₀ ℓ h₁ h₂
    (exists_unitary_exponentialPolynomial_sub j hHM s ℓ hs hA hL0 hL hCfin hCinv hCgr
      f₁ hf₁ f₂ hf₂)

end Expansion

end Langlands.HarishChandraSchwartz
