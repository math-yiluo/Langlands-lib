import Langlands.HarmonicAnalysis.HarishChandraSchwartz.FiniteFunctionExpansion
import Langlands.HarmonicAnalysis.HarishChandraSchwartz.ExponentDirectSum
import Mathlib.Algebra.Group.ForwardDiff
import Mathlib.Algebra.MvPolynomial.Funext
import Mathlib.LinearAlgebra.Eigenspace.Minpoly
import Mathlib.RingTheory.Polynomial.Basic

/-! # Uniqueness of the expansions of finite functions on `A_M` (Waldspurger, I.2)

Waldspurger, I.2 (printed pp. 242–243), in the abstract setting of `FiniteFunctionExpansion`: a
commutative group `A`, an additive `H_M : A → E` into a real vector space and linear forms `ℓ_i`
with `ℓ_i(H_M(s(n))) = n_i` for a homomorphism `s : ℤ^d → A`.

* `expansionCoeff_eq_zero_of_exponentialPolynomial_eq_zero`: uniqueness of the expansion
  `f(a) = ∑_j χ_j(a) Q_j(H_M(a))`;
* `finiteCoeff`: the polynomial `P_{ψ,f}` of the source, with `finiteCoeff_eq_expansionCoeff`;
* `exponentialTerm_finiteCoeff_mem`, `character_mem_of_finiteCoeff_ne_zero`: the membership
  assertions for the minimal set `𝒳`;
* `exists_common_expansion`: one finite minimal `𝒳` and one degree bound for all of a
  finite-dimensional space `V`;
* `exists_uniform_growth_iff_unitary`: the equivalence of the conditions (1) and (2);
* `translateSpan_uniform_growth_iff`: the last sentence of I.2;
* `exists_apply_eq_of_prod_annihilates` and `exists_exponent_not_mem_of_prod_annihilates`: a
  corrected form of the assertion `𝒳 ⊂ 𝒴` and a counterexample to it as printed.
-/

noncomputable section

open Polynomial fwdDiff

namespace Langlands.HarishChandraSchwartz

open Langlands.IntegerLattice Langlands.HarmonicAnalysis.GroupAction

universe u

section LinePolynomial

variable {ι : Type*}

/-- The restriction `z ↦ P(x + z v)` of a polynomial in the coordinates to a complex line, as a
polynomial in one variable. -/
def linePolynomial (x v : ι → ℂ) (P : MvPolynomial ι ℂ) : ℂ[X] :=
  MvPolynomial.aeval (fun i => C (x i) + C (v i) * X) P

theorem eval_linePolynomial (x v : ι → ℂ) (P : MvPolynomial ι ℂ) (z : ℂ) :
    (linePolynomial x v P).eval z = MvPolynomial.eval (fun i => x i + z * v i) P := by
  rw [linePolynomial, ← Polynomial.coe_aeval_eq_eval, MvPolynomial.comp_aeval_apply]
  have hf : (fun i => (Polynomial.aeval z) (C (x i) + C (v i) * X)) =
      fun i => x i + z * v i := by
    funext i
    simp
    ring
  rw [hf, MvPolynomial.aeval_eq_eval]

theorem natDegree_linePolynomial_le (x v : ι → ℂ) (P : MvPolynomial ι ℂ) :
    (linePolynomial x v P).natDegree ≤ P.totalDegree := by
  have := MvPolynomial.aeval_natDegree_le (m := P.totalDegree) (n := 1) P le_rfl
    (fun i => C (x i) + C (v i) * X) (fun i => by
      refine (natDegree_add_le _ _).trans (max_le (by simp) ?_)
      exact (natDegree_C_mul_le _ _).trans (by simp))
  simpa [linePolynomial] using this

/-- The difference operator `Q ↦ Q(X + h) - Q` on polynomials in the coordinates. -/
def coordinateDifference (h : ι → ℂ) : MvPolynomial ι ℂ →ₗ[ℂ] MvPolynomial ι ℂ :=
  (MvPolynomial.aeval (fun i => MvPolynomial.X i + MvPolynomial.C (h i))).toLinearMap -
    LinearMap.id

theorem eval_coordinateDifference (h y : ι → ℂ) (Q : MvPolynomial ι ℂ) :
    MvPolynomial.eval y (coordinateDifference h Q) =
      MvPolynomial.eval (y + h) Q - MvPolynomial.eval y Q := by
  simp only [coordinateDifference, LinearMap.sub_apply, AlgHom.toLinearMap_apply,
    LinearMap.id_apply, map_sub]
  congr 1
  rw [← MvPolynomial.aeval_eq_eval, MvPolynomial.comp_aeval_apply]
  have hf : (fun i => (MvPolynomial.aeval y) (MvPolynomial.X i + MvPolynomial.C (h i))) =
      y + h := by
    funext i
    simp
  rw [hf, MvPolynomial.aeval_eq_eval]

theorem eval_linePolynomial_coordinateDifference (y h : ι → ℂ) (Q : MvPolynomial ι ℂ) :
    (linePolynomial y h (coordinateDifference h Q)).eval =
      Δ_[1] (linePolynomial y h Q).eval := by
  funext z
  rw [fwdDiff, eval_linePolynomial, eval_linePolynomial, eval_linePolynomial,
    eval_coordinateDifference]
  have hf : (fun i => y i + z * h i) + h = fun i => y i + (z + 1) * h i := by
    funext i
    simp only [Pi.add_apply]
    ring
  rw [hf]

theorem eval_linePolynomial_pow_coordinateDifference (y h : ι → ℂ) (k : ℕ) :
    ∀ Q : MvPolynomial ι ℂ, (linePolynomial y h ((coordinateDifference h ^ k) Q)).eval =
      Δ_[1]^[k] (linePolynomial y h Q).eval := by
  induction k with
  | zero => intro Q; simp
  | succ k ih =>
    intro Q
    rw [pow_succ, Module.End.mul_apply, ih, Function.iterate_succ_apply,
      eval_linePolynomial_coordinateDifference]

theorem eval_pow_coordinateDifference_eq_zero (h y : ι → ℂ) {k : ℕ} {Q : MvPolynomial ι ℂ}
    (hk : Q.totalDegree < k) :
    MvPolynomial.eval y ((coordinateDifference h ^ k) Q) = 0 := by
  have h0 : MvPolynomial.eval y ((coordinateDifference h ^ k) Q) =
      (linePolynomial y h ((coordinateDifference h ^ k) Q)).eval 0 := by
    rw [eval_linePolynomial]
    simp only [zero_mul, add_zero]
  have h1 := congrFun (eval_linePolynomial_pow_coordinateDifference y h k Q) 0
  rw [h0, h1, Polynomial.fwdDiff_iter_eq_zero_of_degree_lt
    ((natDegree_linePolynomial_le y h Q).trans_lt hk)]
  rfl

end LinePolynomial

section Terms

variable {A : Type u} [CommGroup A] {E : Type*} [AddCommGroup E] [Module ℝ E] {ι : Type*}

/-- The complex coordinates `(ℓ_i(H_M(a)))_i` of `H_M(a)`. -/
def coordinates (HM : A → E) (ℓ : ι → Module.Dual ℝ E) (a : A) : ι → ℂ :=
  fun i => ((ℓ i (HM a) : ℝ) : ℂ)

theorem coordinates_mul {HM : A → E} (hHM : ∀ a b, HM (a * b) = HM a + HM b)
    (ℓ : ι → Module.Dual ℝ E) (a b : A) :
    coordinates HM ℓ (a * b) = coordinates HM ℓ a + coordinates HM ℓ b := by
  funext i
  simp [coordinates, hHM]

/-- One term `a ↦ χ(a) Q(H_M(a))` of the expansion of Waldspurger, I.2. -/
def exponentialTerm (HM : A → E) (ℓ : ι → Module.Dual ℝ E) (χ : A →* ℂˣ)
    (Q : MvPolynomial ι ℂ) : A → ℂ :=
  fun a => (χ a : ℂ) * MvPolynomial.eval (coordinates HM ℓ a) Q

theorem exponentialPolynomial_eq_sum (HM : A → E) (ℓ : ι → Module.Dual ℝ E) {κ : Type*}
    [Fintype κ] (χ : κ → A →* ℂˣ) (Q : κ → MvPolynomial ι ℂ) :
    exponentialPolynomial HM ℓ χ Q = ∑ j, exponentialTerm HM ℓ (χ j) (Q j) := by
  funext a
  simp only [exponentialPolynomial, Finset.sum_apply, exponentialTerm]
  rfl

theorem exponentialTerm_add (HM : A → E) (ℓ : ι → Module.Dual ℝ E) (χ : A →* ℂˣ)
    (P Q : MvPolynomial ι ℂ) :
    exponentialTerm HM ℓ χ (P + Q) = exponentialTerm HM ℓ χ P + exponentialTerm HM ℓ χ Q := by
  funext a
  simp [exponentialTerm, mul_add]

theorem exponentialTerm_smul (HM : A → E) (ℓ : ι → Module.Dual ℝ E) (χ : A →* ℂˣ) (c : ℂ)
    (Q : MvPolynomial ι ℂ) :
    exponentialTerm HM ℓ χ (c • Q) = c • exponentialTerm HM ℓ χ Q := by
  funext a
  simp only [exponentialTerm, MvPolynomial.smul_eval, smul_eq_mul, Pi.smul_apply]
  ring

theorem exponentialTerm_zero (HM : A → E) (ℓ : ι → Module.Dual ℝ E) (χ : A →* ℂˣ) :
    exponentialTerm HM ℓ χ 0 = 0 := by
  funext a
  simp [exponentialTerm]

theorem exponentialTerm_sum (HM : A → E) (ℓ : ι → Module.Dual ℝ E) (χ : A →* ℂˣ)
    {κ : Type*} (s : Finset κ) (Q : κ → MvPolynomial ι ℂ) :
    exponentialTerm HM ℓ χ (∑ j ∈ s, Q j) = ∑ j ∈ s, exponentialTerm HM ℓ χ (Q j) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [exponentialTerm_zero]
  | insert j s hj ih => rw [Finset.sum_insert hj, Finset.sum_insert hj, exponentialTerm_add, ih]

/-- The right translation by `b` minus `χ(b)` acts on `χ · (Q ∘ H_M)` through the difference
operator of step `H_M(b)`. -/
theorem rightFunctions_sub_smul_exponentialTerm {HM : A → E}
    (hHM : ∀ a b, HM (a * b) = HM a + HM b) (ℓ : ι → Module.Dual ℝ E) (χ : A →* ℂˣ)
    (Q : MvPolynomial ι ℂ) (b : A) :
    (rightFunctions b - (χ b : ℂ) • 1 : Module.End ℂ (A → ℂ)) (exponentialTerm HM ℓ χ Q) =
      (χ b : ℂ) • exponentialTerm HM ℓ χ
        (coordinateDifference (coordinates HM ℓ b) Q) := by
  funext a
  simp only [LinearMap.sub_apply, LinearMap.smul_apply, Module.End.one_apply, Pi.sub_apply,
    Pi.smul_apply, smul_eq_mul, rightFunctions_apply, exponentialTerm, map_mul, Units.val_mul,
    coordinates_mul hHM, eval_coordinateDifference]
  ring

theorem pow_rightFunctions_sub_smul_exponentialTerm {HM : A → E}
    (hHM : ∀ a b, HM (a * b) = HM a + HM b) (ℓ : ι → Module.Dual ℝ E) (χ : A →* ℂˣ)
    (b : A) (k : ℕ) :
    ∀ Q : MvPolynomial ι ℂ,
      ((rightFunctions b - (χ b : ℂ) • 1 : Module.End ℂ (A → ℂ)) ^ k)
          (exponentialTerm HM ℓ χ Q) =
        (χ b : ℂ) ^ k • exponentialTerm HM ℓ χ
          ((coordinateDifference (coordinates HM ℓ b) ^ k) Q) := by
  induction k with
  | zero => intro Q; simp
  | succ k ih =>
    intro Q
    have e1 : ((rightFunctions b - (χ b : ℂ) • 1 : Module.End ℂ (A → ℂ)) ^ (k + 1))
        (exponentialTerm HM ℓ χ Q) =
          ((rightFunctions b - (χ b : ℂ) • 1 : Module.End ℂ (A → ℂ)) ^ k)
            ((rightFunctions b - (χ b : ℂ) • 1 : Module.End ℂ (A → ℂ))
              (exponentialTerm HM ℓ χ Q)) := by
      rw [pow_succ, Module.End.mul_apply]
    rw [e1, rightFunctions_sub_smul_exponentialTerm hHM, map_smul, ih, smul_smul,
      pow_succ (coordinateDifference _) k, Module.End.mul_apply, ← pow_succ']

/-- `χ · (Q ∘ H_M)` is a generalized eigenvector of every right translation `ρ(b)`, for the
eigenvalue `χ(b)`. -/
theorem exponentialTerm_mem_jointGenEigenspace {HM : A → E}
    (hHM : ∀ a b, HM (a * b) = HM a + HM b) (ℓ : ι → Module.Dual ℝ E) (χ : A →* ℂˣ)
    (Q : MvPolynomial ι ℂ) :
    exponentialTerm HM ℓ χ Q ∈
      jointGenEigenspace (rightFunctions (G := A)) (fun a => (χ a : ℂ)) := by
  rw [mem_jointGenEigenspace]
  intro b
  refine ⟨Q.totalDegree + 1, ?_⟩
  rw [pow_rightFunctions_sub_smul_exponentialTerm hHM]
  have : exponentialTerm HM ℓ χ
      ((coordinateDifference (coordinates HM ℓ b) ^ (Q.totalDegree + 1)) Q) = 0 := by
    funext a
    simp only [exponentialTerm, Pi.zero_apply]
    rw [eval_pow_coordinateDifference_eq_zero _ _ (Nat.lt_succ_self _), mul_zero]
  rw [this, smul_zero]

end Terms

section Uniqueness

open scoped Classical

variable {A : Type u} [CommGroup A] {E : Type*} [AddCommGroup E] [Module ℝ E]

/-- A polynomial in the coordinates vanishing at `H_M(a)` for every `a` is zero, when
`ℓ_i(H_M(s(n))) = n_i` for a homomorphism `s : ℤ^d → A`. -/
theorem eq_zero_of_forall_eval_coordinates {HM : A → E} {d : ℕ} (s : Lattice d →* A)
    (ℓ : Fin d → Module.Dual ℝ E) (hs : ∀ n i, ℓ i (HM (s n)) = (n.toAdd i : ℝ))
    {P : MvPolynomial (Fin d) ℂ} (h : ∀ a, MvPolynomial.eval (coordinates HM ℓ a) P = 0) :
    P = 0 := by
  refine MvPolynomial.funext_set (fun _ => Set.range (Int.cast : ℤ → ℂ))
    (fun _ => Set.infinite_range_of_injective Int.cast_injective) fun x hx => ?_
  have hx' : ∀ i, ∃ m : ℤ, (m : ℂ) = x i := fun i => hx i (Set.mem_univ i)
  choose m hm using hx'
  have hxc : x = coordinates HM ℓ (s (Multiplicative.ofAdd m)) := by
    funext i
    simp only [coordinates, hs, toAdd_ofAdd, Complex.ofReal_intCast]
    exact (hm i).symm
  rw [hxc, h, map_zero]

/-- A single term `χ · (Q ∘ H_M)` vanishes only for `Q = 0`. -/
theorem eq_zero_of_exponentialTerm_eq_zero {HM : A → E} {d : ℕ} (s : Lattice d →* A)
    (ℓ : Fin d → Module.Dual ℝ E) (hs : ∀ n i, ℓ i (HM (s n)) = (n.toAdd i : ℝ))
    {χ : A →* ℂˣ} {Q : MvPolynomial (Fin d) ℂ} (h : exponentialTerm HM ℓ χ Q = 0) : Q = 0 := by
  refine eq_zero_of_forall_eval_coordinates s ℓ hs fun a => ?_
  have := congr_fun h a
  simp only [exponentialTerm, Pi.zero_apply, mul_eq_zero, Units.ne_zero, false_or] at this
  exact this

variable {κ : Type*} [Fintype κ] {ι : Type*}

/-- The coefficient polynomial of a character `ψ` in an expansion `∑_j χ_j (Q_j ∘ H_M)`: the sum
of the `Q_j` with `χ_j = ψ`. -/
def expansionCoeff (χ : κ → A →* ℂˣ) (Q : κ → MvPolynomial ι ℂ) (ψ : A →* ℂˣ) :
    MvPolynomial ι ℂ :=
  ∑ j ∈ Finset.univ.filter (fun j => χ j = ψ), Q j

theorem expansionCoeff_eq_zero_of_notMem {χ : κ → A →* ℂˣ} (Q : κ → MvPolynomial ι ℂ)
    {ψ : A →* ℂˣ} (hψ : ψ ∉ Set.range χ) : expansionCoeff χ Q ψ = 0 := by
  refine Finset.sum_eq_zero fun j hj => ?_
  exact absurd ⟨j, (Finset.mem_filter.1 hj).2⟩ hψ

/-- The expansion regrouped by characters. -/
theorem exponentialPolynomial_eq_sum_expansionCoeff (HM : A → E) (ℓ : ι → Module.Dual ℝ E)
    (χ : κ → A →* ℂˣ) (Q : κ → MvPolynomial ι ℂ) :
    exponentialPolynomial HM ℓ χ Q =
      ∑ ψ ∈ Finset.univ.image χ, exponentialTerm HM ℓ ψ (expansionCoeff χ Q ψ) := by
  rw [exponentialPolynomial_eq_sum]
  rw [← Finset.sum_fiberwise_of_maps_to (s := Finset.univ) (t := Finset.univ.image χ) (g := χ)
    (fun j _ => Finset.mem_image_of_mem χ (Finset.mem_univ j))]
  refine Finset.sum_congr rfl fun ψ _ => ?_
  rw [expansionCoeff, exponentialTerm_sum]
  refine Finset.sum_congr rfl fun j hj => ?_
  rw [(Finset.mem_filter.1 hj).2]

theorem coe_injective_units_monoidHom :
    Function.Injective (fun (χ : A →* ℂˣ) (a : A) => (χ a : ℂ)) := by
  intro χ ψ h
  ext a
  exact congr_fun h a

/-- **Uniqueness of the expansion** (Waldspurger, I.2). If `∑_j χ_j(a) Q_j(H_M(a)) = 0` for every
`a`, then for every character `ψ` the sum of the `Q_j` with `χ_j = ψ` is zero. -/
theorem expansionCoeff_eq_zero_of_exponentialPolynomial_eq_zero {HM : A → E}
    (hHM : ∀ a b, HM (a * b) = HM a + HM b) {d : ℕ} (s : Lattice d →* A)
    (ℓ : Fin d → Module.Dual ℝ E) (hs : ∀ n i, ℓ i (HM (s n)) = (n.toAdd i : ℝ))
    (χ : κ → A →* ℂˣ) (Q : κ → MvPolynomial (Fin d) ℂ)
    (h : ∀ a, exponentialPolynomial HM ℓ χ Q a = 0) (ψ : A →* ℂˣ) :
    expansionCoeff χ Q ψ = 0 := by
  by_cases hψ : ψ ∈ Set.range χ
  swap
  · exact expansionCoeff_eq_zero_of_notMem Q hψ
  have hind : iSupIndep ((jointGenEigenspace (rightFunctions (G := A))) ∘
      (fun (χ : A →* ℂˣ) (a : A) => (χ a : ℂ))) :=
    (iSupIndep_jointGenEigenspace _).comp coe_injective_units_monoidHom
  have hsum : ∑ ψ ∈ Finset.univ.image χ,
      exponentialTerm HM ℓ ψ (expansionCoeff χ Q ψ) = 0 := by
    rw [← exponentialPolynomial_eq_sum_expansionCoeff]
    funext a
    exact h a
  have hmem : ψ ∈ Finset.univ.image χ := by
    obtain ⟨j, rfl⟩ := hψ
    exact Finset.mem_image_of_mem χ (Finset.mem_univ j)
  have hzero := (iSupIndep_iff_finsetSum_eq_zero_imp_eq_zero _).1 hind (Finset.univ.image χ)
    (fun ψ => exponentialTerm HM ℓ ψ (expansionCoeff χ Q ψ))
    (fun ψ _ => exponentialTerm_mem_jointGenEigenspace hHM ℓ ψ _) hsum ψ hmem
  exact eq_zero_of_exponentialTerm_eq_zero s ℓ hs hzero

/-- An expansion with pairwise distinct characters vanishes only if all its polynomials do. -/
theorem eq_zero_of_exponentialPolynomial_eq_zero {HM : A → E}
    (hHM : ∀ a b, HM (a * b) = HM a + HM b) {d : ℕ} (s : Lattice d →* A)
    (ℓ : Fin d → Module.Dual ℝ E) (hs : ∀ n i, ℓ i (HM (s n)) = (n.toAdd i : ℝ))
    {χ : κ → A →* ℂˣ} (hχ : Function.Injective χ) (Q : κ → MvPolynomial (Fin d) ℂ)
    (h : ∀ a, exponentialPolynomial HM ℓ χ Q a = 0) (j : κ) : Q j = 0 := by
  have key := expansionCoeff_eq_zero_of_exponentialPolynomial_eq_zero hHM s ℓ hs χ Q h (χ j)
  have hfilter : Finset.univ.filter (fun i => χ i = χ j) = {j} := by
    ext i
    simp [hχ.eq_iff]
  rwa [expansionCoeff, hfilter, Finset.sum_singleton] at key

theorem expansionCoeff_sumElim {κ' : Type*} [Fintype κ'] (χ₁ : κ → A →* ℂˣ)
    (χ₂ : κ' → A →* ℂˣ) (Q₁ : κ → MvPolynomial ι ℂ) (Q₂ : κ' → MvPolynomial ι ℂ)
    (ψ : A →* ℂˣ) :
    expansionCoeff (Sum.elim χ₁ χ₂) (Sum.elim Q₁ Q₂) ψ =
      expansionCoeff χ₁ Q₁ ψ + expansionCoeff χ₂ Q₂ ψ := by
  simp only [expansionCoeff, Finset.sum_filter, Fintype.sum_sum_type, Sum.elim_inl,
    Sum.elim_inr]
  rfl

theorem expansionCoeff_neg (χ : κ → A →* ℂˣ) (Q : κ → MvPolynomial ι ℂ) (ψ : A →* ℂˣ) :
    expansionCoeff χ (fun j => -Q j) ψ = -expansionCoeff χ Q ψ := by
  simp only [expansionCoeff, Finset.sum_neg_distrib]

theorem exponentialPolynomial_sumElim {κ' : Type*} [Fintype κ'] (HM : A → E)
    (ℓ : ι → Module.Dual ℝ E) (χ₁ : κ → A →* ℂˣ) (χ₂ : κ' → A →* ℂˣ)
    (Q₁ : κ → MvPolynomial ι ℂ) (Q₂ : κ' → MvPolynomial ι ℂ) (a : A) :
    exponentialPolynomial HM ℓ (Sum.elim χ₁ χ₂) (Sum.elim Q₁ Q₂) a =
      exponentialPolynomial HM ℓ χ₁ Q₁ a + exponentialPolynomial HM ℓ χ₂ Q₂ a := by
  simp only [exponentialPolynomial, Fintype.sum_sum_type, Sum.elim_inl, Sum.elim_inr]

/-- Two expansions of the same function have the same coefficient polynomial for every
character. -/
theorem expansionCoeff_eq_of_exponentialPolynomial_eq {HM : A → E}
    (hHM : ∀ a b, HM (a * b) = HM a + HM b) {d : ℕ} (s : Lattice d →* A)
    (ℓ : Fin d → Module.Dual ℝ E) (hs : ∀ n i, ℓ i (HM (s n)) = (n.toAdd i : ℝ))
    {κ' : Type*} [Fintype κ'] (χ : κ → A →* ℂˣ) (Q : κ → MvPolynomial (Fin d) ℂ)
    (χ' : κ' → A →* ℂˣ) (Q' : κ' → MvPolynomial (Fin d) ℂ)
    (h : ∀ a, exponentialPolynomial HM ℓ χ Q a = exponentialPolynomial HM ℓ χ' Q' a)
    (ψ : A →* ℂˣ) : expansionCoeff χ Q ψ = expansionCoeff χ' Q' ψ := by
  have h0 := expansionCoeff_eq_zero_of_exponentialPolynomial_eq_zero hHM s ℓ hs
    (Sum.elim χ χ') (Sum.elim Q (fun j => -Q' j)) (fun a => by
      rw [exponentialPolynomial_sumElim, h a]
      simp only [exponentialPolynomial, map_neg, mul_neg, Finset.sum_neg_distrib,
        add_neg_cancel]) ψ
  rw [expansionCoeff_sumElim, expansionCoeff_neg] at h0
  exact sub_eq_zero.1 (by rw [sub_eq_add_neg]; exact h0)

end Uniqueness

section Coefficients

open scoped Classical

variable {A : Type u} [CommGroup A] {E : Type*} [AddCommGroup E] [Module ℝ E] {d : ℕ}

/-- `f` has an expansion `f(a) = ∑_j χ_j(a) Q_j(H_M(a))` with finitely many characters. -/
def HasFiniteExpansion (HM : A → E) (ℓ : Fin d → Module.Dual ℝ E) (f : A → ℂ) : Prop :=
  ∃ (n : ℕ) (χ : Fin n → A →* ℂˣ) (Q : Fin n → MvPolynomial (Fin d) ℂ),
    ∀ a, f a = exponentialPolynomial HM ℓ χ Q a

/-- Waldspurger's polynomial `P_{ψ,f}` of I.2: the coefficient of the character `ψ` in an
expansion of `f` (independent of the expansion by
`finiteCoeff_eq_expansionCoeff`), and `0` if `f` has no expansion. -/
def finiteCoeff (HM : A → E) (ℓ : Fin d → Module.Dual ℝ E) (f : A → ℂ) (ψ : A →* ℂˣ) :
    MvPolynomial (Fin d) ℂ :=
  if h : HasFiniteExpansion HM ℓ f then
    expansionCoeff h.choose_spec.choose h.choose_spec.choose_spec.choose ψ
  else 0

variable {HM : A → E} (hHM : ∀ a b, HM (a * b) = HM a + HM b) (s : Lattice d →* A)
  (ℓ : Fin d → Module.Dual ℝ E) (hs : ∀ n i, ℓ i (HM (s n)) = (n.toAdd i : ℝ))
include hHM hs

/-- The coefficient `P_{ψ,f}` computed from any expansion of `f`. -/
theorem finiteCoeff_eq_expansionCoeff {κ : Type*} [Fintype κ] {f : A → ℂ}
    (χ : κ → A →* ℂˣ) (Q : κ → MvPolynomial (Fin d) ℂ)
    (hf : ∀ a, f a = exponentialPolynomial HM ℓ χ Q a) (ψ : A →* ℂˣ) :
    finiteCoeff HM ℓ f ψ = expansionCoeff χ Q ψ := by
  have hexp : HasFiniteExpansion HM ℓ f := by
    obtain ⟨n, ⟨e⟩⟩ : ∃ n, Nonempty (κ ≃ Fin n) := ⟨_, ⟨Fintype.equivFin κ⟩⟩
    refine ⟨n, fun j => χ (e.symm j), fun j => Q (e.symm j), fun a => ?_⟩
    rw [hf a, exponentialPolynomial_comp_equiv]
  simp only [finiteCoeff, hexp, ↓reduceDIte]
  exact expansionCoeff_eq_of_exponentialPolynomial_eq hHM s ℓ hs _ _ χ Q
    (fun a => (hexp.choose_spec.choose_spec.choose_spec a).symm.trans (hf a)) ψ

/-- An `A`-finite function is the sum of its terms `ψ · (P_{ψ,f} ∘ H_M)` over the characters of
any of its expansions. -/
theorem eq_sum_finiteCoeff {κ : Type*} [Fintype κ] {f : A → ℂ}
    (χ : κ → A →* ℂˣ) (Q : κ → MvPolynomial (Fin d) ℂ)
    (hf : ∀ a, f a = exponentialPolynomial HM ℓ χ Q a) :
    f = ∑ ψ ∈ Finset.univ.image χ, exponentialTerm HM ℓ ψ (finiteCoeff HM ℓ f ψ) := by
  funext a
  rw [hf a, exponentialPolynomial_eq_sum_expansionCoeff]
  refine congrFun (Finset.sum_congr rfl fun ψ _ => ?_) a
  rw [finiteCoeff_eq_expansionCoeff hHM s ℓ hs χ Q hf]

theorem finiteCoeff_eq_zero_of_notMem {κ : Type*} [Fintype κ] {f : A → ℂ}
    (χ : κ → A →* ℂˣ) (Q : κ → MvPolynomial (Fin d) ℂ)
    (hf : ∀ a, f a = exponentialPolynomial HM ℓ χ Q a) {ψ : A →* ℂˣ}
    (hψ : ψ ∉ Set.range χ) : finiteCoeff HM ℓ f ψ = 0 := by
  rw [finiteCoeff_eq_expansionCoeff hHM s ℓ hs χ Q hf]
  exact expansionCoeff_eq_zero_of_notMem Q hψ

omit hHM hs in
theorem HasFiniteExpansion.add {f g : A → ℂ} (hf : HasFiniteExpansion HM ℓ f)
    (hg : HasFiniteExpansion HM ℓ g) : HasFiniteExpansion HM ℓ (f + g) := by
  obtain ⟨n₁, χ₁, Q₁, h₁⟩ := hf
  obtain ⟨n₂, χ₂, Q₂, h₂⟩ := hg
  refine ⟨n₁ + n₂, Fin.append χ₁ χ₂, Fin.append Q₁ Q₂, fun a => ?_⟩
  rw [exponentialPolynomial_append, Pi.add_apply, h₁, h₂]

omit hHM hs in
theorem HasFiniteExpansion.smul {f : A → ℂ} (hf : HasFiniteExpansion HM ℓ f) (c : ℂ) :
    HasFiniteExpansion HM ℓ (c • f) := by
  obtain ⟨n, χ, Q, h⟩ := hf
  refine ⟨n, χ, fun j => c • Q j, fun a => ?_⟩
  simp only [Pi.smul_apply, smul_eq_mul, h a, exponentialPolynomial, MvPolynomial.smul_eval,
    Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  ring

omit hHM hs in
theorem hasFiniteExpansion_zero : HasFiniteExpansion HM ℓ (0 : A → ℂ) :=
  ⟨0, Fin.elim0, Fin.elim0, fun a => by simp [exponentialPolynomial]⟩

theorem finiteCoeff_add {f g : A → ℂ} (hf : HasFiniteExpansion HM ℓ f)
    (hg : HasFiniteExpansion HM ℓ g) (ψ : A →* ℂˣ) :
    finiteCoeff HM ℓ (f + g) ψ = finiteCoeff HM ℓ f ψ + finiteCoeff HM ℓ g ψ := by
  obtain ⟨n₁, χ₁, Q₁, h₁⟩ := hf
  obtain ⟨n₂, χ₂, Q₂, h₂⟩ := hg
  have h : ∀ a, (f + g) a = exponentialPolynomial HM ℓ (Sum.elim χ₁ χ₂) (Sum.elim Q₁ Q₂) a :=
    fun a => by rw [exponentialPolynomial_sumElim, Pi.add_apply, h₁, h₂]
  rw [finiteCoeff_eq_expansionCoeff hHM s ℓ hs _ _ h, finiteCoeff_eq_expansionCoeff hHM s ℓ hs _ _ h₁,
    finiteCoeff_eq_expansionCoeff hHM s ℓ hs _ _ h₂, expansionCoeff_sumElim]

theorem finiteCoeff_smul {f : A → ℂ} (hf : HasFiniteExpansion HM ℓ f) (c : ℂ)
    (ψ : A →* ℂˣ) : finiteCoeff HM ℓ (c • f) ψ = c • finiteCoeff HM ℓ f ψ := by
  obtain ⟨n, χ, Q, h⟩ := hf
  have h' : ∀ a, (c • f) a = exponentialPolynomial HM ℓ χ (fun j => c • Q j) a := by
    intro a
    simp only [Pi.smul_apply, smul_eq_mul, h a, exponentialPolynomial, MvPolynomial.smul_eval,
      Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    ring
  rw [finiteCoeff_eq_expansionCoeff hHM s ℓ hs _ _ h', finiteCoeff_eq_expansionCoeff hHM s ℓ hs _ _ h,
    expansionCoeff, expansionCoeff, Finset.smul_sum]

omit hHM hs in
theorem hasFiniteExpansion_sum {κ : Type*} (t : Finset κ) (c : κ → ℂ) (g : κ → A → ℂ)
    (hg : ∀ i ∈ t, HasFiniteExpansion HM ℓ (g i)) :
    HasFiniteExpansion HM ℓ (∑ i ∈ t, c i • g i) := by
  induction t using Finset.induction_on with
  | empty => simpa using hasFiniteExpansion_zero ℓ
  | insert i t hi ih =>
    rw [Finset.sum_insert hi]
    exact HasFiniteExpansion.add ℓ
      (HasFiniteExpansion.smul ℓ (hg i (Finset.mem_insert_self i t)) (c i))
      (ih fun j hj => hg j (Finset.mem_insert_of_mem hj))

theorem finiteCoeff_sum {κ : Type*} (t : Finset κ) (c : κ → ℂ) (g : κ → A → ℂ)
    (hg : ∀ i ∈ t, HasFiniteExpansion HM ℓ (g i)) (ψ : A →* ℂˣ) :
    finiteCoeff HM ℓ (∑ i ∈ t, c i • g i) ψ = ∑ i ∈ t, c i • finiteCoeff HM ℓ (g i) ψ := by
  induction t using Finset.induction_on with
  | empty =>
    simp only [Finset.sum_empty]
    rw [finiteCoeff_eq_expansionCoeff hHM s ℓ hs (Fin.elim0 : Fin 0 → A →* ℂˣ) Fin.elim0
      (fun a => by simp [exponentialPolynomial])]
    simp [expansionCoeff]
  | insert i t hi ih =>
    rw [Finset.sum_insert hi, Finset.sum_insert hi,
      finiteCoeff_add hHM s ℓ hs
        (HasFiniteExpansion.smul ℓ (hg i (Finset.mem_insert_self i t)) (c i))
        (hasFiniteExpansion_sum ℓ t c g fun j hj => hg j (Finset.mem_insert_of_mem hj)),
      finiteCoeff_smul hHM s ℓ hs (hg i (Finset.mem_insert_self i t)),
      ih fun j hj => hg j (Finset.mem_insert_of_mem hj)]

end Coefficients

section JointEigenvector

variable {A : Type*} [CommGroup A] {Y : Type*} [AddCommGroup Y] [Module ℂ Y]

/-- A nonzero finite-dimensional subspace of a joint generalized eigenspace of a commutative
family `T`, stable under `T`, contains a joint eigenvector. -/
theorem exists_ne_zero_forall_apply_eq_smul (T : A →* Module.End ℂ Y) (χ : A → ℂ) :
    ∀ (n : ℕ) (W : Submodule ℂ Y), Module.finrank ℂ W = n → FiniteDimensional ℂ W →
      (∀ a, ∀ x ∈ W, T a x ∈ W) → W ≤ jointGenEigenspace T χ → W ≠ ⊥ →
        ∃ w ∈ W, w ≠ 0 ∧ ∀ a, T a w = χ a • w := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro W hn hfin hW hWχ hW0
    by_cases hall : ∀ a, ∀ x ∈ W, T a x = χ a • x
    · obtain ⟨w, hw, hw0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hW0
      exact ⟨w, hw, hw0, fun a => hall a w hw⟩
    push Not at hall
    obtain ⟨b, x₀, hx₀, hne⟩ := hall
    have hNW : ∀ m : ℕ, ∀ x ∈ W, ((T b - χ b • 1) ^ m) x ∈ W := by
      intro m
      induction m with
      | zero => intro x hx; simpa using hx
      | succ m ihm =>
        intro x hx
        rw [pow_succ, Module.End.mul_apply]
        refine ihm _ ?_
        simp only [LinearMap.sub_apply, LinearMap.smul_apply, Module.End.one_apply]
        exact W.sub_mem (hW b x hx) (W.smul_mem _ hx)
    have hcomm : ∀ a, Commute (T a) (T b - χ b • 1) := fun a =>
      (commute_jointFamily T a b).sub_right ((Commute.one_right (T a)).smul_right (χ b))
    let W' : Submodule ℂ Y := W ⊓ LinearMap.ker (T b - χ b • 1)
    have hW'stable : ∀ a, ∀ x ∈ W', T a x ∈ W' := by
      intro a x hx
      refine ⟨hW a x hx.1, LinearMap.mem_ker.2 ?_⟩
      have : (T b - χ b • 1) (T a x) = T a ((T b - χ b • 1) x) := by
        rw [← Module.End.mul_apply, ← (hcomm a).eq, Module.End.mul_apply]
      rw [this, LinearMap.mem_ker.1 hx.2, map_zero]
    have hW'0 : W' ≠ ⊥ := by
      obtain ⟨y, hy, hy0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hW0
      obtain ⟨k, hk⟩ := (mem_jointGenEigenspace.1 (hWχ hy)) b
      obtain ⟨m, hm0, hm⟩ := exists_pow_apply_eigen (T b) (χ b) hy0 hk
      refine (Submodule.ne_bot_iff _).2
        ⟨((T b - χ b • 1) ^ m) y, ⟨hNW m y hy, LinearMap.mem_ker.2 ?_⟩, hm0⟩
      rw [LinearMap.sub_apply, LinearMap.smul_apply, Module.End.one_apply, hm, sub_self]
    have hlt : W' < W := by
      refine lt_of_le_of_ne inf_le_left fun heq => hne ?_
      have hx' : x₀ ∈ W' := heq ▸ hx₀
      have := LinearMap.mem_ker.1 hx'.2
      rwa [LinearMap.sub_apply, LinearMap.smul_apply, Module.End.one_apply, sub_eq_zero] at this
    have hfin' : FiniteDimensional ℂ W' := Submodule.finiteDimensional_of_le inf_le_left
    obtain ⟨w, hw, hw0, hwa⟩ := ih _ (hn ▸ Submodule.finrank_lt_finrank_of_lt hlt) W' rfl hfin'
      hW'stable (inf_le_left.trans hWχ) hW'0
    exact ⟨w, hw.1, hw0, hwa⟩

/-- The joint eigenvector of `exists_ne_zero_forall_apply_eq_smul`, for `W = V ⊓ Y_χ`. -/
theorem exists_eigenvector_of_inf_jointGenEigenspace_ne_bot (T : A →* Module.End ℂ Y)
    (V : Submodule ℂ Y) [FiniteDimensional ℂ V] (hV : ∀ a, ∀ x ∈ V, T a x ∈ V) {χ : A → ℂ}
    (hχ : V ⊓ jointGenEigenspace T χ ≠ ⊥) :
    ∃ w ∈ V, w ≠ 0 ∧ ∀ a, T a w = χ a • w := by
  obtain ⟨w, hw, hw0, hwa⟩ := exists_ne_zero_forall_apply_eq_smul T χ _ _ rfl
    (Submodule.finiteDimensional_of_le inf_le_left)
    (fun a x hx => ⟨hV a x hx.1, apply_mem_jointGenEigenspace T a hx.2⟩) inf_le_right hχ
  exact ⟨w, hw.1, hw0, hwa⟩

end JointEigenvector

section FiniteSpaces

open scoped Classical

variable {A : Type u} [CommGroup A] {E : Type*} [AddCommGroup E] [Module ℝ E] {d : ℕ}

/-- For an injective `Φ`, a sum over the `ψ'` with `Φ ψ' = Φ ψ` has at most the term `ψ`. -/
theorem sum_filter_coe_eq {M : Type*} [AddCommMonoid M] (S : Finset (A →* ℂˣ))
    (F : (A →* ℂˣ) → M) (ψ : A →* ℂˣ) :
    ∑ ψ' ∈ S.filter (fun ψ' => (fun a => (ψ' a : ℂ)) = fun a => (ψ a : ℂ)), F ψ' =
      if ψ ∈ S then F ψ else 0 := by
  rw [Finset.filter_congr (q := fun ψ' => ψ' = ψ) fun ψ' _ =>
    coe_injective_units_monoidHom.eq_iff, Finset.sum_filter, Finset.sum_ite_eq']

variable {HM : A → E} (hHM : ∀ a b, HM (a * b) = HM a + HM b) (s : Lattice d →* A)
  (ℓ : Fin d → Module.Dual ℝ E) (hs : ∀ n i, ℓ i (HM (s n)) = (n.toAdd i : ℝ))
include hHM hs

/-- **Waldspurger, I.2**: for `f` in a finite-dimensional space `V` stable under right
translations, each term `ψ · (P_{ψ,f} ∘ H_M)` of the expansion of `f` belongs to `V`. -/
theorem exponentialTerm_finiteCoeff_mem (V : Submodule ℂ (A → ℂ)) [FiniteDimensional ℂ V]
    (hV : ∀ b, ∀ g ∈ V, rightFunctions b g ∈ V) {f : A → ℂ} (hfV : f ∈ V)
    (hf : HasFiniteExpansion HM ℓ f) (ψ : A →* ℂˣ) :
    exponentialTerm HM ℓ ψ (finiteCoeff HM ℓ f ψ) ∈ V := by
  obtain ⟨n, χ, Q, hfQ⟩ := hf
  by_cases hψ : ψ ∈ Finset.univ.image χ
  swap
  · rw [finiteCoeff_eq_zero_of_notMem hHM s ℓ hs χ Q hfQ (fun ⟨j, hj⟩ => hψ (hj ▸
      Finset.mem_image_of_mem χ (Finset.mem_univ j))), exponentialTerm_zero]
    exact V.zero_mem
  obtain ⟨c, hcmem, hcsum⟩ :=
    exists_sum_mem_jointGenEigenspace (rightFunctions (G := A)) V hV hfV
  let Φ : (A →* ℂˣ) → (A → ℂ) := fun χ a => (χ a : ℂ)
  let S : Finset (A → ℂ) := c.support ∪ (Finset.univ.image χ).image Φ
  let w : (A → ℂ) → (A → ℂ) := fun φ =>
    ∑ ψ' ∈ (Finset.univ.image χ).filter (fun ψ' => Φ ψ' = φ),
      exponentialTerm HM ℓ ψ' (finiteCoeff HM ℓ f ψ')
  have hmem : ∀ φ ∈ S, c φ ∈ jointGenEigenspace (rightFunctions (G := A)) φ ∧
      w φ ∈ jointGenEigenspace (rightFunctions (G := A)) φ := by
    intro φ _
    refine ⟨(hcmem φ).2, Submodule.sum_mem _ fun ψ' hψ' => ?_⟩
    rw [← (Finset.mem_filter.1 hψ').2]
    exact exponentialTerm_mem_jointGenEigenspace hHM ℓ ψ' _
  have hsum : ∑ φ ∈ S, c φ = ∑ φ ∈ S, w φ := by
    have h1 : ∑ φ ∈ S, c φ = f := by
      rw [← hcsum]
      exact (Finsupp.sum_of_support_subset c Finset.subset_union_left (fun _ x => x)
        fun _ _ => rfl).symm
    have h2 : ∑ φ ∈ S, w φ = f := by
      rw [Finset.sum_fiberwise_of_maps_to (fun ψ' hψ' => Finset.mem_union_right _
        (Finset.mem_image_of_mem Φ hψ'))]
      exact (eq_sum_finiteCoeff hHM s ℓ hs χ Q hfQ).symm
    rw [h1, h2]
  have hΦψ : Φ ψ ∈ S := Finset.mem_union_right _ (Finset.mem_image_of_mem Φ hψ)
  have heq := (iSupIndep_iff_finsetSum_eq_imp_eq _).1 (iSupIndep_jointGenEigenspace _) S c w
    hmem hsum (Φ ψ) hΦψ
  have hw : w (Φ ψ) = exponentialTerm HM ℓ ψ (finiteCoeff HM ℓ f ψ) := by
    simp only [w, Φ]
    rw [sum_filter_coe_eq]
    simp only [hψ, ↓reduceIte]
  rw [← hw, ← heq]
  exact (hcmem (Φ ψ)).1

/-- The nonzero coefficients of an element of `V` give nonzero vectors of `V ⊓ V_ψ`, and
conversely when every element of `V` has an expansion: `ψ` belongs to the minimal set `𝒳` of
I.2 if and only if it is an exponent of the right translations on `V`. -/
theorem exists_finiteCoeff_ne_zero_iff (V : Submodule ℂ (A → ℂ)) [FiniteDimensional ℂ V]
    (hV : ∀ b, ∀ g ∈ V, rightFunctions b g ∈ V)
    (hexp : ∀ g ∈ V, HasFiniteExpansion HM ℓ g) (ψ : A →* ℂˣ) :
    (∃ f ∈ V, finiteCoeff HM ℓ f ψ ≠ 0) ↔
      V ⊓ jointGenEigenspace (rightFunctions (G := A)) (fun a => (ψ a : ℂ)) ≠ ⊥ := by
  constructor
  · rintro ⟨f, hfV, hψ⟩
    refine (Submodule.ne_bot_iff _).2 ⟨exponentialTerm HM ℓ ψ (finiteCoeff HM ℓ f ψ),
      ⟨exponentialTerm_finiteCoeff_mem hHM s ℓ hs V hV hfV (hexp f hfV) ψ,
        exponentialTerm_mem_jointGenEigenspace hHM ℓ ψ _⟩, fun h0 => hψ ?_⟩
    exact eq_zero_of_exponentialTerm_eq_zero s ℓ hs h0
  · intro hne
    obtain ⟨g, ⟨hgV, hgψ⟩, hg0⟩ := (Submodule.ne_bot_iff _).1 hne
    refine ⟨g, hgV, fun hc => hg0 ?_⟩
    obtain ⟨n, χ, Q, hgQ⟩ := hexp g hgV
    let Φ : (A →* ℂˣ) → (A → ℂ) := fun χ a => (χ a : ℂ)
    let S : Finset (A → ℂ) := insert (Φ ψ) ((Finset.univ.image χ).image Φ)
    let v : (A → ℂ) → (A → ℂ) := fun φ => if φ = Φ ψ then g else 0
    let w : (A → ℂ) → (A → ℂ) := fun φ =>
      ∑ ψ' ∈ (Finset.univ.image χ).filter (fun ψ' => Φ ψ' = φ),
        exponentialTerm HM ℓ ψ' (finiteCoeff HM ℓ g ψ')
    have hmem : ∀ φ ∈ S, v φ ∈ jointGenEigenspace (rightFunctions (G := A)) φ ∧
        w φ ∈ jointGenEigenspace (rightFunctions (G := A)) φ := by
      intro φ _
      refine ⟨?_, Submodule.sum_mem _ fun ψ' hψ' => ?_⟩
      · simp only [v]
        split_ifs with h
        · rw [h]; exact hgψ
        · exact Submodule.zero_mem _
      · rw [← (Finset.mem_filter.1 hψ').2]
        exact exponentialTerm_mem_jointGenEigenspace hHM ℓ ψ' _
    have hsum : ∑ φ ∈ S, v φ = ∑ φ ∈ S, w φ := by
      have h1 : ∑ φ ∈ S, v φ = g := by
        simp only [v]
        rw [Finset.sum_ite_eq' S (Φ ψ) (fun _ => g)]
        simp only [S, Finset.mem_insert_self, ↓reduceIte]
      have h2 : ∑ φ ∈ S, w φ = g := by
        rw [Finset.sum_fiberwise_of_maps_to (fun ψ' hψ' => Finset.mem_insert_of_mem
          (Finset.mem_image_of_mem Φ hψ'))]
        exact (eq_sum_finiteCoeff hHM s ℓ hs χ Q hgQ).symm
      rw [h1, h2]
    have heq := (iSupIndep_iff_finsetSum_eq_imp_eq _).1 (iSupIndep_jointGenEigenspace _) S v w
      hmem hsum (Φ ψ) (Finset.mem_insert_self _ _)
    have hv : v (Φ ψ) = g := by simp only [v, ↓reduceIte]
    have hw : w (Φ ψ) = 0 := by
      simp only [w, Φ]
      rw [sum_filter_coe_eq]
      split_ifs
      · rw [hc, exponentialTerm_zero]
      · rfl
    rw [← hv, heq, hw]

/-- **Waldspurger, I.2**: if `P_{ψ,f} ≠ 0` for some `f` in `V` (`ψ` belongs to the minimal `𝒳`),
then the character `a ↦ ψ(a)` belongs to `V`. -/
theorem character_mem_of_finiteCoeff_ne_zero (V : Submodule ℂ (A → ℂ)) [FiniteDimensional ℂ V]
    (hV : ∀ b, ∀ g ∈ V, rightFunctions b g ∈ V) {f : A → ℂ} (hfV : f ∈ V)
    (hf : HasFiniteExpansion HM ℓ f) {ψ : A →* ℂˣ} (hψ : finiteCoeff HM ℓ f ψ ≠ 0) :
    (fun a => (ψ a : ℂ)) ∈ V := by
  have hne : V ⊓ jointGenEigenspace (rightFunctions (G := A)) (fun a => (ψ a : ℂ)) ≠ ⊥ := by
    refine (Submodule.ne_bot_iff _).2 ⟨exponentialTerm HM ℓ ψ (finiteCoeff HM ℓ f ψ),
      ⟨exponentialTerm_finiteCoeff_mem hHM s ℓ hs V hV hfV hf ψ,
        exponentialTerm_mem_jointGenEigenspace hHM ℓ ψ _⟩, fun h0 => hψ ?_⟩
    exact eq_zero_of_exponentialTerm_eq_zero s ℓ hs h0
  obtain ⟨w, hwV, hw0, hwa⟩ :=
    exists_eigenvector_of_inf_jointGenEigenspace_ne_bot (rightFunctions (G := A)) V hV hne
  have hval : ∀ a, w a = (ψ a : ℂ) * w 1 := by
    intro a
    have := congrFun (hwa a) 1
    rwa [rightFunctions_apply, one_mul, Pi.smul_apply, smul_eq_mul] at this
  have hw1 : w 1 ≠ 0 := by
    intro h1
    apply hw0
    funext a
    rw [hval a, h1, mul_zero, Pi.zero_apply]
  have : (fun a => (ψ a : ℂ)) = (w 1)⁻¹ • w := by
    funext a
    rw [Pi.smul_apply, smul_eq_mul, hval a]
    field_simp
  rw [this]
  exact V.smul_mem _ hwV

/-- **Waldspurger, I.2**: a common finite set `𝒳` and a common degree bound for all of `V`. If
every element of a finite-dimensional `V` has an expansion, there are a finite set `𝒳` of
characters, each with `P_{ψ,f} ≠ 0` for some `f ∈ V` (`𝒳` is minimal), and `D ∈ ℕ`, such that
every `f ∈ V` is `∑_{ψ ∈ 𝒳} ψ · (P_{ψ,f} ∘ H_M)` with `deg P_{ψ,f} ≤ D` and `P_{ψ,f} = 0` for
`ψ ∉ 𝒳`. -/
theorem exists_common_expansion (V : Submodule ℂ (A → ℂ)) [FiniteDimensional ℂ V]
    (hexp : ∀ g ∈ V, HasFiniteExpansion HM ℓ g) :
    ∃ (X : Finset (A →* ℂˣ)) (D : ℕ), (∀ ψ ∈ X, ∃ f ∈ V, finiteCoeff HM ℓ f ψ ≠ 0) ∧
      ∀ f ∈ V, (∀ ψ, ψ ∉ X → finiteCoeff HM ℓ f ψ = 0) ∧
        (∀ ψ, (finiteCoeff HM ℓ f ψ).totalDegree ≤ D) ∧
          f = ∑ ψ ∈ X, exponentialTerm HM ℓ ψ (finiteCoeff HM ℓ f ψ) := by
  let b := Module.finBasis ℂ V
  choose n χ Q hQ using fun i => hexp ((b i : V) : A → ℂ) (b i).2
  let X₀ : Finset (A →* ℂˣ) := Finset.univ.biUnion fun i => Finset.univ.image (χ i)
  let X : Finset (A →* ℂˣ) := X₀.filter fun ψ => ∃ f ∈ V, finiteCoeff HM ℓ f ψ ≠ 0
  let D : ℕ := Finset.univ.sup fun i =>
    (Finset.univ.image (χ i)).sup fun ψ => (finiteCoeff HM ℓ ((b i : V) : A → ℂ) ψ).totalDegree
  refine ⟨X, D, fun ψ hψ => (Finset.mem_filter.1 hψ).2, fun f hf => ?_⟩
  have hsum : f = ∑ i, b.repr ⟨f, hf⟩ i • ((b i : V) : A → ℂ) := by
    have := congrArg (fun x : V => (x : A → ℂ)) (b.sum_repr ⟨f, hf⟩)
    simp only [Submodule.coe_sum, Submodule.coe_smul] at this
    exact this.symm
  have hcoeff : ∀ ψ, finiteCoeff HM ℓ f ψ =
      ∑ i, b.repr ⟨f, hf⟩ i • finiteCoeff HM ℓ ((b i : V) : A → ℂ) ψ := by
    intro ψ
    conv_lhs => rw [hsum]
    exact finiteCoeff_sum hHM s ℓ hs _ _ _ (fun i _ => hexp _ (b i).2) ψ
  have hzero : ∀ ψ, ψ ∉ X₀ → finiteCoeff HM ℓ f ψ = 0 := by
    intro ψ hψ
    rw [hcoeff ψ]
    refine Finset.sum_eq_zero fun i _ => ?_
    rw [finiteCoeff_eq_zero_of_notMem hHM s ℓ hs (χ i) (Q i) (hQ i) ?_, smul_zero]
    rintro ⟨j, rfl⟩
    exact hψ (Finset.mem_biUnion.2
      ⟨i, Finset.mem_univ _, Finset.mem_image_of_mem _ (Finset.mem_univ j)⟩)
  have hzeroX : ∀ ψ, ψ ∉ X → finiteCoeff HM ℓ f ψ = 0 := by
    intro ψ hψ
    by_cases h0 : ψ ∈ X₀
    · by_contra hne
      exact hψ (Finset.mem_filter.2 ⟨h0, f, hf, hne⟩)
    · exact hzero ψ h0
  refine ⟨hzeroX, fun ψ => ?_, ?_⟩
  · rw [hcoeff ψ]
    refine (MvPolynomial.totalDegree_finsetSum _ _).trans (Finset.sup_le fun i _ => ?_)
    refine (MvPolynomial.totalDegree_smul_le _ _).trans ?_
    by_cases hψi : ψ ∈ Finset.univ.image (χ i)
    · exact (Finset.le_sup (f := fun ψ =>
        (finiteCoeff HM ℓ ((b i : V) : A → ℂ) ψ).totalDegree) hψi).trans
        (Finset.le_sup (f := fun i => (Finset.univ.image (χ i)).sup fun ψ =>
          (finiteCoeff HM ℓ ((b i : V) : A → ℂ) ψ).totalDegree) (Finset.mem_univ i))
    · rw [finiteCoeff_eq_zero_of_notMem hHM s ℓ hs (χ i) (Q i) (hQ i) fun ⟨j, hj⟩ =>
        hψi (hj ▸ Finset.mem_image_of_mem _ (Finset.mem_univ j))]
      simp
  · obtain ⟨m, χf, Qf, hfQ⟩ := hexp f hf
    have hX : ∀ ψ ∈ Finset.univ.image χf ∪ X, ψ ∉ X →
        exponentialTerm HM ℓ ψ (finiteCoeff HM ℓ f ψ) = 0 := fun ψ _ hψ => by
      rw [hzeroX ψ hψ, exponentialTerm_zero]
    calc f = ∑ ψ ∈ Finset.univ.image χf, exponentialTerm HM ℓ ψ (finiteCoeff HM ℓ f ψ) :=
          eq_sum_finiteCoeff hHM s ℓ hs χf Qf hfQ
      _ = ∑ ψ ∈ Finset.univ.image χf ∪ X,
          exponentialTerm HM ℓ ψ (finiteCoeff HM ℓ f ψ) :=
          Finset.sum_subset Finset.subset_union_left fun ψ _ hψ' => by
            rw [finiteCoeff_eq_zero_of_notMem hHM s ℓ hs χf Qf hfQ fun ⟨j, hj⟩ =>
              hψ' (hj ▸ Finset.mem_image_of_mem χf (Finset.mem_univ j)), exponentialTerm_zero]
      _ = ∑ ψ ∈ X, exponentialTerm HM ℓ ψ (finiteCoeff HM ℓ f ψ) :=
          (Finset.sum_subset Finset.subset_union_right hX).symm

end FiniteSpaces

section GrowthBounds

variable {A : Type*} {L : A → ℝ}

theorem hasPolynomialGrowth_const (c : ℂ) : HasPolynomialGrowth L (fun _ => c) :=
  ⟨‖c‖, 0, fun a => by simp⟩

/-- Products of functions of polynomial growth have polynomial growth. -/
theorem HasPolynomialGrowth.mul (hL0 : ∀ a, 0 ≤ L a) {φ ψ : A → ℂ}
    (hφ : HasPolynomialGrowth L φ) (hψ : HasPolynomialGrowth L ψ) :
    HasPolynomialGrowth L (φ * ψ) := by
  obtain ⟨C₁, r₁, h₁⟩ := hφ
  obtain ⟨C₂, r₂, h₂⟩ := hψ
  refine ⟨max C₁ 0 * max C₂ 0, r₁ + r₂, fun a => ?_⟩
  have hp : ∀ r : ℕ, 0 ≤ (1 + L a) ^ r := fun r => pow_nonneg (by linarith [hL0 a]) r
  have e₁ : ‖φ a‖ ≤ max C₁ 0 * (1 + L a) ^ r₁ :=
    (h₁ a).trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (hp _))
  have e₂ : ‖ψ a‖ ≤ max C₂ 0 * (1 + L a) ^ r₂ :=
    (h₂ a).trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (hp _))
  calc ‖(φ * ψ) a‖ = ‖φ a‖ * ‖ψ a‖ := by rw [Pi.mul_apply, norm_mul]
    _ ≤ (max C₁ 0 * (1 + L a) ^ r₁) * (max C₂ 0 * (1 + L a) ^ r₂) :=
        mul_le_mul e₁ e₂ (norm_nonneg _) (mul_nonneg (le_max_right _ _) (hp _))
    _ = max C₁ 0 * max C₂ 0 * (1 + L a) ^ (r₁ + r₂) := by rw [pow_add]; ring

/-- Finite sums of functions of polynomial growth have polynomial growth. -/
theorem HasPolynomialGrowth.sum (hL0 : ∀ a, 0 ≤ L a) {κ : Type*} (t : Finset κ)
    (F : κ → A → ℂ) (h : ∀ j ∈ t, HasPolynomialGrowth L (F j)) :
    HasPolynomialGrowth L (∑ j ∈ t, F j) := by
  classical
  induction t using Finset.induction_on with
  | empty => simpa using (hasPolynomialGrowth_zero : HasPolynomialGrowth L (0 : A → ℂ))
  | insert j t hj ih =>
    rw [Finset.sum_insert hj]
    exact HasPolynomialGrowth.add hL0 (h j (Finset.mem_insert_self j t))
      (ih fun i hi => h i (Finset.mem_insert_of_mem hi))

/-- In a finite-dimensional space of functions of polynomial growth, one exponent `r` serves for
all functions (condition (1) of Waldspurger, I.2). -/
theorem exists_uniform_hasPolynomialGrowth (hL0 : ∀ a, 0 ≤ L a) (V : Submodule ℂ (A → ℂ))
    [FiniteDimensional ℂ V] (h : ∀ f ∈ V, HasPolynomialGrowth L f) :
    ∃ r : ℕ, ∀ f ∈ V, ∃ C : ℝ, ∀ a, ‖f a‖ ≤ C * (1 + L a) ^ r := by
  let b := Module.finBasis ℂ V
  choose C r hCr using fun i => h ((b i : V) : A → ℂ) (b i).2
  refine ⟨Finset.univ.sup r, fun f hf => ?_⟩
  refine ⟨∑ i, ‖b.repr ⟨f, hf⟩ i‖ * max (C i) 0, fun a => ?_⟩
  have hfa : f a = ∑ i, b.repr ⟨f, hf⟩ i * ((b i : V) : A → ℂ) a := by
    have := congrArg (fun x : V => (x : A → ℂ) a) (b.sum_repr ⟨f, hf⟩)
    simp only [Submodule.coe_sum, Submodule.coe_smul, Finset.sum_apply, Pi.smul_apply,
      smul_eq_mul] at this
    exact this.symm
  have h1 : 1 ≤ 1 + L a := by linarith [hL0 a]
  rw [hfa, Finset.sum_mul]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun i _ => ?_)
  rw [norm_mul, mul_assoc]
  refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
  calc ‖((b i : V) : A → ℂ) a‖ ≤ C i * (1 + L a) ^ r i := hCr i a
    _ ≤ max (C i) 0 * (1 + L a) ^ r i :=
        mul_le_mul_of_nonneg_right (le_max_left _ _) (pow_nonneg (by linarith) _)
    _ ≤ max (C i) 0 * (1 + L a) ^ Finset.univ.sup r :=
        mul_le_mul_of_nonneg_left (pow_le_pow_right₀ h1 (Finset.le_sup (Finset.mem_univ i)))
          (le_max_right _ _)

end GrowthBounds

section PolynomialGrowth

variable {A : Type u} [CommGroup A] {E : Type*} [AddCommGroup E] [Module ℝ E] {ι : Type*}
  {HM : A → E} {ℓ : ι → Module.Dual ℝ E} {L : A → ℝ}

omit [CommGroup A] in
/-- A polynomial in the coordinates of `H_M` has polynomial growth when the coordinates are
bounded by `C (1 + L)`. -/
theorem hasPolynomialGrowth_eval_coordinates (hL0 : ∀ a, 0 ≤ L a)
    (hHL : ∃ C : ℝ, ∀ a i, |ℓ i (HM a)| ≤ C * (1 + L a)) (P : MvPolynomial ι ℂ) :
    HasPolynomialGrowth L (fun a => MvPolynomial.eval (coordinates HM ℓ a) P) := by
  obtain ⟨C, hC⟩ := hHL
  induction P using MvPolynomial.induction_on with
  | C c => simpa using hasPolynomialGrowth_const (L := L) c
  | add p q hp hq =>
    convert HasPolynomialGrowth.add hL0 hp hq using 1
    funext a
    simp
  | mul_X p i hp =>
    have hi : HasPolynomialGrowth L (fun a => coordinates HM ℓ a i) :=
      ⟨C, 1, fun a => by simpa [coordinates, Complex.norm_real, Real.norm_eq_abs] using hC a i⟩
    convert HasPolynomialGrowth.mul hL0 hp hi using 1
    funext a
    simp

/-- A term `ψ · (P ∘ H_M)` with a unitary character `ψ` has polynomial growth. -/
theorem hasPolynomialGrowth_exponentialTerm (hL0 : ∀ a, 0 ≤ L a)
    (hHL : ∃ C : ℝ, ∀ a i, |ℓ i (HM a)| ≤ C * (1 + L a)) {ψ : A →* ℂˣ}
    (hψ : ∀ a, ‖(ψ a : ℂ)‖ = 1) (P : MvPolynomial ι ℂ) :
    HasPolynomialGrowth L (exponentialTerm HM ℓ ψ P) := by
  obtain ⟨C, r, h⟩ := hasPolynomialGrowth_eval_coordinates hL0 hHL P
  exact ⟨C, r, fun a => by simpa [exponentialTerm, norm_mul, hψ a] using h a⟩

end PolynomialGrowth

section GrowthEquivalence

variable {A : Type u} [CommGroup A] {L : A → ℝ}

/-- **Waldspurger, I.2, (1) ⇒ (2)**, for an exponent `χ` of the right translations on a
finite-dimensional stable `V` all of whose elements have polynomial growth: `|χ| = 1`. -/
theorem norm_eq_one_of_hasPolynomialGrowth_of_exponent (hL0 : ∀ a, 0 ≤ L a)
    (hL : ∀ a b, L (a * b) ≤ L a + L b) (V : Submodule ℂ (A → ℂ)) [FiniteDimensional ℂ V]
    (hV : ∀ b, ∀ g ∈ V, rightFunctions b g ∈ V) (hgr : ∀ f ∈ V, HasPolynomialGrowth L f)
    {χ : A → ℂ} (hχ : V ⊓ jointGenEigenspace (rightFunctions (G := A)) χ ≠ ⊥) (a : A) :
    ‖χ a‖ = 1 := by
  obtain ⟨w, hwV, hw0, hwa⟩ :=
    exists_eigenvector_of_inf_jointGenEigenspace_ne_bot (rightFunctions (G := A)) V hV hχ
  have hz : ∀ x a', w (a' * x) = χ x * w a' := fun x a' => by
    have := congrFun (hwa x) a'
    rwa [rightFunctions_apply, Pi.smul_apply, smul_eq_mul] at this
  have h1 := norm_le_one_of_hasPolynomialGrowth hL0 hL (hgr w hwV) hw0 (hz a)
  have h2 := norm_le_one_of_hasPolynomialGrowth hL0 hL (hgr w hwV) hw0 (hz a⁻¹)
  obtain ⟨a', ha'⟩ : ∃ a', w a' ≠ 0 := by
    by_contra hcon
    push Not at hcon
    exact hw0 (funext hcon)
  have hmul : χ a⁻¹ * χ a = 1 := by
    have e := hz a⁻¹ (a' * a)
    rw [hz a a', mul_assoc, mul_inv_cancel, mul_one, ← mul_assoc] at e
    have := mul_right_cancel₀ ha' (e.symm.trans (one_mul (w a')).symm)
    exact this
  have hnorm : ‖χ a⁻¹‖ * ‖χ a‖ = 1 := by rw [← norm_mul, hmul, norm_one]
  refine le_antisymm h1 ?_
  nlinarith [norm_nonneg (χ a), norm_nonneg (χ a⁻¹)]

/-- The last sentence of Waldspurger, I.2: for an `A`-finite `f`, condition (1) for `V_f` is
equivalent to the polynomial growth of `f` itself. -/
theorem translateSpan_uniform_growth_iff (hL0 : ∀ a, 0 ≤ L a)
    (hL : ∀ a b, L (a * b) ≤ L a + L b) {f : A → ℂ} (hf : FiniteDimensional ℂ (translateSpan f)) :
    (∃ r : ℕ, ∀ φ ∈ translateSpan f, ∃ C : ℝ, ∀ a, ‖φ a‖ ≤ C * (1 + L a) ^ r) ↔
      ∃ (r : ℕ) (C : ℝ), ∀ a, ‖f a‖ ≤ C * (1 + L a) ^ r := by
  constructor
  · rintro ⟨r, hr⟩
    obtain ⟨C, hC⟩ := hr f (mem_translateSpan_self f)
    exact ⟨r, C, hC⟩
  · rintro ⟨r, C, hC⟩
    exact exists_uniform_hasPolynomialGrowth hL0 (translateSpan f) fun φ hφ =>
      hasPolynomialGrowth_of_mem_translateSpan hL0 hL ⟨C, r, hC⟩ hφ

variable {E : Type*} [AddCommGroup E] [Module ℝ E] {d : ℕ} {HM : A → E}
  (hHM : ∀ a b, HM (a * b) = HM a + HM b) (s : Lattice d →* A)
  (ℓ : Fin d → Module.Dual ℝ E) (hs : ∀ n i, ℓ i (HM (s n)) = (n.toAdd i : ℝ))
include hHM hs

open scoped Classical in
/-- **Waldspurger, I.2, (2) ⇒ (1)** for one function: an `A`-finite function all of whose
characters with nonzero coefficient are unitary has polynomial growth, when the coordinates of
`H_M` are bounded by `C (1 + L)`. -/
theorem hasPolynomialGrowth_of_unitary (hL0 : ∀ a, 0 ≤ L a)
    (hHL : ∃ C : ℝ, ∀ a i, |ℓ i (HM a)| ≤ C * (1 + L a)) {f : A → ℂ}
    (hf : HasFiniteExpansion HM ℓ f)
    (hunit : ∀ ψ : A →* ℂˣ, finiteCoeff HM ℓ f ψ ≠ 0 → ∀ a, ‖(ψ a : ℂ)‖ = 1) :
    HasPolynomialGrowth L f := by
  obtain ⟨n, χ, Q, hfQ⟩ := hf
  rw [eq_sum_finiteCoeff hHM s ℓ hs χ Q hfQ]
  refine HasPolynomialGrowth.sum hL0 _ _ fun ψ _ => ?_
  by_cases h0 : finiteCoeff HM ℓ f ψ = 0
  · rw [h0, exponentialTerm_zero]
    exact hasPolynomialGrowth_zero
  · exact hasPolynomialGrowth_exponentialTerm hL0 hHL (hunit ψ h0) _

/-- **Waldspurger, I.2, the equivalence of (1) and (2).** Let `V` be a finite-dimensional space of
functions on `A`, stable under right translations, every element of which has an expansion, and
let the coordinates of `H_M` be bounded by `C (1 + L)` for a nonnegative subadditive `L`. Then
(1) there is `r ∈ ℕ` such that every `f ∈ V` satisfies `|f(a)| ≤ C_f (1 + L(a))^r` if and only if
(2) every character `ψ` of the minimal set `𝒳` (some `f ∈ V` has `P_{ψ,f} ≠ 0`) is unitary. -/
theorem exists_uniform_growth_iff_unitary (hL0 : ∀ a, 0 ≤ L a)
    (hL : ∀ a b, L (a * b) ≤ L a + L b) (hHL : ∃ C : ℝ, ∀ a i, |ℓ i (HM a)| ≤ C * (1 + L a))
    (V : Submodule ℂ (A → ℂ)) [FiniteDimensional ℂ V]
    (hV : ∀ b, ∀ g ∈ V, rightFunctions b g ∈ V) (hexp : ∀ g ∈ V, HasFiniteExpansion HM ℓ g) :
    (∃ r : ℕ, ∀ f ∈ V, ∃ C : ℝ, ∀ a, ‖f a‖ ≤ C * (1 + L a) ^ r) ↔
      ∀ ψ : A →* ℂˣ, (∃ f ∈ V, finiteCoeff HM ℓ f ψ ≠ 0) → ∀ a, ‖(ψ a : ℂ)‖ = 1 := by
  constructor
  · rintro ⟨r, hr⟩ ψ hψ a
    have hgr : ∀ f ∈ V, HasPolynomialGrowth L f := fun f hf => by
      obtain ⟨C, hC⟩ := hr f hf
      exact ⟨C, r, hC⟩
    exact norm_eq_one_of_hasPolynomialGrowth_of_exponent hL0 hL V hV hgr
      ((exists_finiteCoeff_ne_zero_iff hHM s ℓ hs V hV hexp ψ).1 hψ) a
  · intro hunit
    exact exists_uniform_hasPolynomialGrowth hL0 V fun f hf =>
      hasPolynomialGrowth_of_unitary hHM s ℓ hs hL0 hHL (hexp f hf) fun ψ hψ =>
        hunit ψ ⟨f, hf, hψ⟩

end GrowthEquivalence

section Annihilation

/-- A polynomial in an operator `T` acts on a vector `w` with `T w = μ w` by its value at `μ`. -/
theorem aeval_apply_of_apply_eq_smul {Y : Type*} [AddCommGroup Y] [Module ℂ Y]
    (T : Module.End ℂ Y) {w : Y} {μ : ℂ} (hw : T w = μ • w) (p : ℂ[X]) :
    aeval T p w = p.eval μ • w := by
  by_cases h0 : w = 0
  · simp [h0]
  · exact Module.End.aeval_apply_of_hasEigenvector
      (Module.End.hasEigenvector_iff.2 ⟨Module.End.mem_eigenspace_iff.2 hw, h0⟩)

variable {A : Type u} [CommGroup A]

/-- **A corrected form of the last assertion of Waldspurger, I.2.** If for every `a` the operator
`∏_{ψ ∈ 𝒴} (ρ(a) - ψ(a))^D` kills a finite-dimensional stable `V`, then for every exponent `χ` of
`V` and every `a ∈ A` there is `ψ ∈ 𝒴` with `ψ(a) = χ(a)`. The operator is written as the
polynomial `∏_{ψ ∈ 𝒴} (X - ψ(a))^D` evaluated at `ρ(a)`. The printed conclusion `𝒳 ⊂ 𝒴` (one
`ψ` for all `a`) does not follow: see `exists_exponent_not_mem_of_prod_annihilates`. -/
theorem exists_apply_eq_of_prod_annihilates (V : Submodule ℂ (A → ℂ)) [FiniteDimensional ℂ V]
    (hV : ∀ b, ∀ g ∈ V, rightFunctions b g ∈ V) (Y : Finset (A →* ℂˣ)) (D : ℕ)
    (hY : ∀ a, ∀ g ∈ V, aeval (rightFunctions a) (∏ ψ ∈ Y, (X - C (ψ a : ℂ)) ^ D) g = 0)
    {χ : A → ℂ} (hχ : V ⊓ jointGenEigenspace (rightFunctions (G := A)) χ ≠ ⊥) (a : A) :
    ∃ ψ ∈ Y, (ψ a : ℂ) = χ a := by
  obtain ⟨w, hwV, hw0, hwa⟩ :=
    exists_eigenvector_of_inf_jointGenEigenspace_ne_bot (rightFunctions (G := A)) V hV hχ
  have h := hY a w hwV
  rw [aeval_apply_of_apply_eq_smul _ (hwa a), smul_eq_zero, eval_prod] at h
  rcases h with h | h
  · obtain ⟨ψ, hψ, h0⟩ := Finset.prod_eq_zero_iff.1 h
    rw [eval_pow, eval_sub, eval_X, eval_C] at h0
    exact ⟨ψ, hψ, (sub_eq_zero.1 (eq_zero_of_pow_eq_zero h0)).symm⟩
  · exact absurd h hw0

/-- The character `n ↦ (-1)^{⟨v, n⟩}` of `ℤ²`. -/
def signCharacter (v : Fin 2 → ℤ) : Lattice 2 →* ℂˣ where
  toFun n := (-1 : ℂˣ) ^ (∑ i, v i * n.toAdd i)
  map_one' := by simp
  map_mul' m n := by
    simp only [toAdd_mul, Pi.add_apply, mul_add, Finset.sum_add_distrib, zpow_add]

theorem coe_signCharacter (v : Fin 2 → ℤ) (n : Lattice 2) :
    (signCharacter v n : ℂ) = (-1 : ℂ) ^ (v 0 * n.toAdd 0 + v 1 * n.toAdd 1) := by
  simp [signCharacter, Fin.sum_univ_two]

/-- **The inclusion `𝒳 ⊂ 𝒴` of Waldspurger, I.2, fails as printed.** On `A = ℤ²` (for instance
the image of `A_M = (F^×)²` under the valuation), with `H_M` the identity coordinates, let `V` be
the constant functions and `𝒴` the three characters `(-1)^{n₀}`, `(-1)^{n₁}`, `(-1)^{n₀+n₁}`.
Every `a` lies in the kernel of one of them, so `∏_{ψ ∈ 𝒴} (ρ(a) - ψ(a))` kills `V` for every
`a` (`D = 1`), but the trivial character, which has a nonzero coefficient on `1 ∈ V`, is not in
`𝒴`. -/
theorem exists_exponent_not_mem_of_prod_annihilates :
    ∃ (V : Submodule ℂ (Lattice 2 → ℂ)) (Y : Finset (Lattice 2 →* ℂˣ)),
      FiniteDimensional ℂ V ∧ (∀ b, ∀ g ∈ V, rightFunctions b g ∈ V) ∧
      (∀ a, ∀ g ∈ V, aeval (rightFunctions a) (∏ ψ ∈ Y, (X - C (ψ a : ℂ)) ^ 1) g = 0) ∧
      ∃ χ : Lattice 2 →* ℂˣ, χ ∉ Y ∧ (∃ f ∈ V, finiteCoeff (E := Fin 2 → ℝ)
        (fun n i => (n.toAdd i : ℝ)) (fun i => LinearMap.proj i) f χ ≠ 0) := by
  classical
  let one : Lattice 2 → ℂ := fun _ => 1
  let V : Submodule ℂ (Lattice 2 → ℂ) := Submodule.span ℂ {one}
  let Y : Finset (Lattice 2 →* ℂˣ) :=
    {signCharacter ![1, 0], signCharacter ![0, 1], signCharacter ![1, 1]}
  have hconst : ∀ g ∈ V, ∀ b, rightFunctions b g = g := by
    intro g hg b
    obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.1 hg
    funext x
    simp [one]
  refine ⟨V, Y, inferInstance, fun b g hg => by rw [hconst g hg b]; exact hg, ?_, 1, ?_, ?_⟩
  · intro a g hg
    have hw : rightFunctions a g = (1 : ℂ) • g := by rw [hconst g hg a, one_smul]
    rw [aeval_apply_of_apply_eq_smul _ hw, eval_prod]
    have hzero : ∏ ψ ∈ Y, ((X - C (ψ a : ℂ)) ^ 1).eval 1 = 0 := by
      have key : ∃ ψ ∈ Y, (ψ a : ℂ) = 1 := by
        rcases Int.even_or_odd (a.toAdd 0) with h0 | h0
        · exact ⟨signCharacter ![1, 0], by simp [Y], by
            rw [coe_signCharacter]; simpa using h0.neg_one_zpow⟩
        rcases Int.even_or_odd (a.toAdd 1) with h1 | h1
        · exact ⟨signCharacter ![0, 1], by simp [Y], by
            rw [coe_signCharacter]; simpa using h1.neg_one_zpow⟩
        · exact ⟨signCharacter ![1, 1], by simp [Y], by
            rw [coe_signCharacter]; simpa using (h0.add_odd h1).neg_one_zpow⟩
      obtain ⟨ψ, hψ, h1⟩ := key
      exact Finset.prod_eq_zero hψ (by rw [eval_pow, eval_sub, eval_X, eval_C, h1, sub_self,
        pow_one])
    rw [hzero, zero_smul]
  · intro h1
    simp only [Y, Finset.mem_insert, Finset.mem_singleton] at h1
    have hval : ∀ v : Fin 2 → ℤ, (1 : Lattice 2 →* ℂˣ) = signCharacter v →
        (1 : ℂ) = (-1 : ℂ) ^ (v 0 * (Multiplicative.toAdd (Multiplicative.ofAdd ![1, 0]) 0) +
          v 1 * (Multiplicative.toAdd (Multiplicative.ofAdd ![1, 0]) 1)) ∧
        (1 : ℂ) = (-1 : ℂ) ^ (v 0 * (Multiplicative.toAdd (Multiplicative.ofAdd ![0, 1]) 0) +
          v 1 * (Multiplicative.toAdd (Multiplicative.ofAdd ![0, 1]) 1)) := by
      intro v hv
      constructor
      · have := congrArg (fun χ : Lattice 2 →* ℂˣ => (χ (Multiplicative.ofAdd ![1, 0]) : ℂ)) hv
        simpa [coe_signCharacter] using this
      · have := congrArg (fun χ : Lattice 2 →* ℂˣ => (χ (Multiplicative.ofAdd ![0, 1]) : ℂ)) hv
        simpa [coe_signCharacter] using this
    rcases h1 with h1 | h1 | h1
    · have := (hval _ h1).1
      norm_num at this
    · have := (hval _ h1).2
      norm_num at this
    · have := (hval _ h1).1
      norm_num at this
  · refine ⟨one, Submodule.mem_span_singleton_self one, ?_⟩
    have hexp : ∀ a, one a = exponentialPolynomial (E := Fin 2 → ℝ)
        (fun n i => (n.toAdd i : ℝ)) (fun i => LinearMap.proj i)
        (fun _ : Fin 1 => (1 : Lattice 2 →* ℂˣ)) (fun _ => 1) a := by
      intro a
      simp [one, exponentialPolynomial]
    rw [finiteCoeff_eq_expansionCoeff (fun a b => by funext i; simp) (MonoidHom.id (Lattice 2))
      (fun i => LinearMap.proj i) (fun n i => by simp) _ _ hexp]
    simp [expansionCoeff]

end Annihilation

end Langlands.HarishChandraSchwartz
