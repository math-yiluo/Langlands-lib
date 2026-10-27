import Langlands.Representation.MatrixCoefficient.IntegerLatticeStatement
import Mathlib.Algebra.MvPolynomial.Rename
import Mathlib.LinearAlgebra.Eigenspace.Triangularizable
import Mathlib.LinearAlgebra.Finsupp.LinearCombination
import Mathlib.Analysis.Complex.Polynomial.Basic

/-! # Proof: exponential-polynomial matrix coefficients on the integer lattice -/

namespace Langlands.IntegerLatticeExponentialPolynomial

open MvPolynomial

/-! ### Binomial coefficients as polynomial functions -/

/-- The binomial polynomial `x ↦ x (x - 1) ⋯ (x - k + 1) / k!`, evaluated on `ℂ`. -/
noncomputable def binomCoeff (k : ℕ) (x : ℂ) : ℂ :=
  ((k.factorial : ℂ))⁻¹ * ∏ i ∈ Finset.range k, (x - i)

@[simp] theorem binomCoeff_zero (x : ℂ) : binomCoeff 0 x = 1 := by
  simp [binomCoeff]

theorem binomCoeff_succ_zero (k : ℕ) : binomCoeff (k + 1) 0 = 0 := by
  simp [binomCoeff, Finset.prod_range_succ']

/-- Pascal's rule, valid at every complex point and so at every integer. -/
theorem binomCoeff_succ_succ (k : ℕ) (x : ℂ) :
    binomCoeff (k + 1) (x + 1) = binomCoeff k x + binomCoeff (k + 1) x := by
  have hP : ∏ i ∈ Finset.range (k + 1), (x + 1 - (i : ℂ)) =
      (∏ i ∈ Finset.range k, (x - (i : ℂ))) * (x + 1) := by
    rw [Finset.prod_range_succ']
    congr 1
    · refine Finset.prod_congr rfl fun i _ => ?_
      push_cast
      ring
    · simp
  unfold binomCoeff
  rw [hP, Finset.prod_range_succ, Nat.factorial_succ]
  have hk : (k.factorial : ℂ) ≠ 0 := by exact_mod_cast k.factorial_ne_zero
  have hk1 : ((k : ℂ) + 1) ≠ 0 := by exact_mod_cast k.succ_ne_zero
  push_cast
  field_simp
  ring

/-- The binomial polynomial in the zeroth variable. -/
noncomputable def binomPoly {d : ℕ} (k : ℕ) : MvPolynomial (Fin (d + 1)) ℂ :=
  C ((k.factorial : ℂ))⁻¹ * ∏ i ∈ Finset.range k, (X 0 - C (i : ℂ))

theorem eval_binomPoly {d : ℕ} (k : ℕ) (n : Fin (d + 1) → ℤ) :
    eval (fun i => (n i : ℂ)) (binomPoly (d := d) k) = binomCoeff k (n 0) := by
  simp [binomPoly, binomCoeff, map_prod]

/-! ### One invertible operator on a generalized eigenvector -/

/-- Two integer-indexed sequences with the same recursion along an injective map agree. -/
theorem int_seq_eq_of_step {V : Type*} {T : V → V} (hT : Function.Injective T)
    {F G : ℤ → V} (h0 : F 0 = G 0) (hF : ∀ m, F (m + 1) = T (F m))
    (hG : ∀ m, G (m + 1) = T (G m)) : ∀ m, F m = G m := by
  intro m
  induction m using Int.induction_on with
  | zero => exact h0
  | succ i ih => rw [hF, hG, ih]
  | pred i ih =>
    apply hT
    rw [← hF, ← hG, sub_add_cancel, ih]

variable {V : Type*} [AddCommGroup V] [Module ℂ V]

/-- Every integer power of an invertible operator, on a generalized eigenvector with nonzero
eigenvalue `μ`, is `μ ^ m` times a finite binomial expansion in the nilpotent part. -/
theorem zpow_apply_of_genEigen (T : (Module.End ℂ V)ˣ) {μ : ℂ} (hμ : μ ≠ 0) {K : ℕ}
    {v : V} (hv : (((T : Module.End ℂ V) - μ • 1) ^ K) v = 0) (m : ℤ) :
    ((T ^ m : (Module.End ℂ V)ˣ) : Module.End ℂ V) v =
      μ ^ m • ∑ k ∈ Finset.range (K + 1),
        binomCoeff k m • ((μ⁻¹ • ((T : Module.End ℂ V) - μ • 1)) ^ k) v := by
  set M : Module.End ℂ V := μ⁻¹ • ((T : Module.End ℂ V) - μ • 1) with hM
  have hTM : ∀ w : V, (T : Module.End ℂ V) w = μ • (w + M w) := by
    intro w
    rw [hM, LinearMap.smul_apply, LinearMap.sub_apply, LinearMap.smul_apply,
      Module.End.one_apply, smul_add, smul_smul, mul_inv_cancel₀ hμ, one_smul]
    abel
  have hMK : (M ^ (K + 1)) v = 0 := by
    have h : (M ^ K) v = 0 := by
      rw [hM, smul_pow, LinearMap.smul_apply, hv, smul_zero]
    rw [pow_succ', Module.End.mul_apply, h, map_zero]
  set S : ℤ → V := fun m => ∑ k ∈ Finset.range (K + 1), binomCoeff k m • (M ^ k) v with hS
  have hSstep : ∀ m : ℤ, S (m + 1) = S m + M (S m) := by
    intro m
    have hMS : M (S m) = ∑ k ∈ Finset.range (K + 1), binomCoeff k m • (M ^ (k + 1)) v := by
      simp only [hS, map_sum, map_smul, pow_succ', Module.End.mul_apply]
    rw [hMS, Finset.sum_range_succ, hMK, smul_zero, add_zero]
    simp only [hS]
    rw [Finset.sum_range_succ', Finset.sum_range_succ' (fun k => binomCoeff k m • (M ^ k) v)]
    push_cast
    simp only [binomCoeff_succ_succ, add_smul, Finset.sum_add_distrib, binomCoeff_zero]
    abel
  refine int_seq_eq_of_step (T := (T : Module.End ℂ V))
    (F := fun m => ((T ^ m : (Module.End ℂ V)ˣ) : Module.End ℂ V) v)
    (G := fun m => μ ^ m • S m) ?_ ?_ ?_ ?_ m
  · intro a b hab
    have h := congrArg (((T⁻¹ : (Module.End ℂ V)ˣ) : Module.End ℂ V)) hab
    simpa only [← Module.End.mul_apply, Units.inv_mul, Module.End.one_apply] using h
  · simp [hS, Finset.sum_range_succ', binomCoeff_succ_zero]
  · intro m
    rw [add_comm, zpow_one_add, Units.val_mul, Module.End.mul_apply]
  · intro m
    show μ ^ (m + 1) • S (m + 1) = (T : Module.End ℂ V) (μ ^ m • S m)
    rw [map_smul, hTM, smul_smul, ← zpow_add_one₀ hμ, hSstep]

/-! ### The span of exponential-polynomial vector functions -/

variable {W : Type*} [AddCommGroup W] [Module ℂ W]

/-- One exponential-polynomial term `n ↦ (χ n * Q n) • w`. -/
noncomputable def term {d : ℕ} (χ : Multiplicative (Fin d → ℤ) →* ℂˣ)
    (Q : MvPolynomial (Fin d) ℂ) (w : W) : (Fin d → ℤ) → W :=
  fun n => ((χ (Multiplicative.ofAdd n) : ℂ) * eval (fun i => (n i : ℂ)) Q) • w

/-- The complex span of all exponential-polynomial terms. -/
noncomputable def space (d : ℕ) (W : Type*) [AddCommGroup W] [Module ℂ W] :
    Submodule ℂ ((Fin d → ℤ) → W) :=
  Submodule.span ℂ {f | ∃ (χ : Multiplicative (Fin d → ℤ) →* ℂˣ)
    (Q : MvPolynomial (Fin d) ℂ) (w : W), term χ Q w = f}

theorem term_mem {d : ℕ} (χ : Multiplicative (Fin d → ℤ) →* ℂˣ) (Q : MvPolynomial (Fin d) ℂ)
    (w : W) : term χ Q w ∈ space d W :=
  Submodule.subset_span ⟨χ, Q, w, rfl⟩

/-- Applying a linear map pointwise preserves exponential-polynomial functions. -/
theorem comp_mem {d : ℕ} {W' : Type*} [AddCommGroup W'] [Module ℂ W'] (ell : W →ₗ[ℂ] W')
    {f : (Fin d → ℤ) → W} (hf : f ∈ space d W) : (fun n => ell (f n)) ∈ space d W' := by
  have hle : space d W ≤ (space d W').comap (ell.compLeft (Fin d → ℤ)) := by
    refine Submodule.span_le.mpr ?_
    rintro _ ⟨χ, Q, w, rfl⟩
    have : ell.compLeft (Fin d → ℤ) (term χ Q w) = term χ Q (ell w) := by
      funext n
      show ell (term χ Q w n) = term χ Q (ell w) n
      simp [term]
    simp only [SetLike.mem_coe, Submodule.mem_comap, this]
    exact term_mem χ Q (ell w)
  exact hle hf

/-- A scalar exponential-polynomial function has the explicit finite form of the target. -/
theorem exists_of_mem {d : ℕ} {f : (Fin d → ℤ) → ℂ} (hf : f ∈ space d ℂ) :
    ∃ (l : ℕ) (χ : Fin l → Multiplicative (Fin d → ℤ) →* ℂˣ)
      (Q : Fin l → MvPolynomial (Fin d) ℂ),
      ∀ n : Fin d → ℤ, f n = ∑ j, (χ j (Multiplicative.ofAdd n) : ℂ) *
        eval (fun i => (n i : ℂ)) (Q j) := by
  obtain ⟨l, a, g, hg⟩ := Submodule.mem_span_set'.mp hf
  choose χ Q w hw using fun j => (g j).2
  refine ⟨l, χ, fun j => C (a j * w j) * Q j, fun n => ?_⟩
  rw [← hg, Finset.sum_apply]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Pi.smul_apply, ← hw j]
  simp only [term, smul_eq_mul, eval_mul, eval_C]
  ring

/-! ### Adjoining one coordinate -/

/-- The character `n ↦ μ ^ n₀ * χ (tail n)` of the larger lattice. -/
def consChar {d : ℕ} (μ : ℂˣ) (χ : Multiplicative (Fin d → ℤ) →* ℂˣ) :
    Multiplicative (Fin (d + 1) → ℤ) →* ℂˣ where
  toFun x := μ ^ (Multiplicative.toAdd x 0) *
    χ (Multiplicative.ofAdd (Fin.tail (Multiplicative.toAdd x)))
  map_one' := by
    simp only [toAdd_one, Pi.zero_apply, zpow_zero, one_mul]
    exact χ.map_one
  map_mul' x y := by
    simp only [toAdd_mul, Pi.add_apply, zpow_add]
    rw [show Fin.tail (Multiplicative.toAdd x + Multiplicative.toAdd y) =
        Fin.tail (Multiplicative.toAdd x) + Fin.tail (Multiplicative.toAdd y) from rfl,
      ofAdd_add, map_mul]
    exact mul_mul_mul_comm _ _ _ _

/-- Multiplying by a one-coordinate exponential-binomial factor in `n₀` and reading the
remaining coordinates as `tail n` maps exponential polynomials in `d` variables to
exponential polynomials in `d + 1` variables. -/
theorem cons_mem {d : ℕ} (μ : ℂˣ) (k : ℕ) {g : (Fin d → ℤ) → W} (hg : g ∈ space d W) :
    (fun n : Fin (d + 1) → ℤ =>
      ((μ : ℂ) ^ (n 0) * binomCoeff k (n 0)) • g (Fin.tail n)) ∈ space (d + 1) W := by
  let Φ : ((Fin d → ℤ) → W) →ₗ[ℂ] ((Fin (d + 1) → ℤ) → W) :=
    { toFun := fun g n => ((μ : ℂ) ^ (n 0) * binomCoeff k (n 0)) • g (Fin.tail n)
      map_add' := by
        intro g₁ g₂
        funext n
        simp [smul_add]
      map_smul' := by
        intro c g
        funext n
        simp [smul_comm c] }
  have hle : space d W ≤ (space (d + 1) W).comap Φ := by
    refine Submodule.span_le.mpr ?_
    rintro _ ⟨χ, Q, w, rfl⟩
    have : Φ (term χ Q w) = term (consChar μ χ) (binomPoly k * rename Fin.succ Q) w := by
      funext n
      simp only [Φ, LinearMap.coe_mk, AddHom.coe_mk, term, consChar, MonoidHom.coe_mk,
        OneHom.coe_mk, toAdd_ofAdd, Units.val_mul, Units.val_zpow_eq_zpow_val, eval_mul,
        eval_binomPoly, eval_rename, smul_smul]
      congr 1
      simp only [Function.comp_def, Fin.tail]
      ring
    simp only [SetLike.mem_coe, Submodule.mem_comap, this]
    exact term_mem _ _ w
  exact hle hg

/-! ### The orbit maps of a lattice representation -/

/-- The inclusion of `ℤ^d` as the tuples with zeroth coordinate `0`. -/
def consZero (d : ℕ) : Multiplicative (Fin d → ℤ) →* Multiplicative (Fin (d + 1) → ℤ) where
  toFun x := Multiplicative.ofAdd (Fin.cons 0 (Multiplicative.toAdd x))
  map_one' := by
    ext i
    refine Fin.cases ?_ (fun j => ?_) i <;> simp
  map_mul' x y := by
    ext i
    refine Fin.cases ?_ (fun j => ?_) i <;> simp

/-- Each lattice element is the product of its tail part and a power of the zeroth generator. -/
theorem ofAdd_eq_consZero_mul (d : ℕ) (n : Fin (d + 1) → ℤ) :
    Multiplicative.ofAdd n = consZero d (Multiplicative.ofAdd (Fin.tail n)) *
      Multiplicative.ofAdd (Pi.single 0 1 : Fin (d + 1) → ℤ) ^ (n 0) := by
  apply Multiplicative.toAdd.injective
  ext i
  refine Fin.cases ?_ (fun j => ?_) i <;>
    simp [consZero, toAdd_zpow, Fin.tail, Fin.succ_ne_zero]

variable [FiniteDimensional ℂ V]

/-- Every orbit map `n ↦ ρ n v` of a finite-dimensional complex lattice representation is an
exponential-polynomial vector function. -/
theorem orbit_mem_space : ∀ (d : ℕ) (ρ : Representation ℂ (Multiplicative (Fin d → ℤ)) V)
    (v : V), (fun n => ρ (Multiplicative.ofAdd n) v) ∈ space d V := by
  intro d
  induction d with
  | zero =>
    intro ρ v
    have : (fun n : Fin 0 → ℤ => ρ (Multiplicative.ofAdd n) v) = term 1 1 v := by
      funext n
      rw [Subsingleton.elim (Multiplicative.ofAdd n) 1, map_one]
      simp [term]
    rw [this]
    exact term_mem 1 1 v
  | succ d ih =>
    intro ρ v
    let ρ' : Representation ℂ (Multiplicative (Fin d → ℤ)) V := ρ.comp (consZero d)
    let T : (Module.End ℂ V)ˣ :=
      ρ.asGroupHom (Multiplicative.ofAdd (Pi.single 0 1 : Fin (d + 1) → ℤ))
    let L : V →ₗ[ℂ] ((Fin (d + 1) → ℤ) → V) :=
      { toFun := fun v n => ρ' (Multiplicative.ofAdd (Fin.tail n))
          (((T ^ (n 0) : (Module.End ℂ V)ˣ) : Module.End ℂ V) v)
        map_add' := by
          intro v₁ v₂
          funext n
          simp
        map_smul' := by
          intro c v
          funext n
          simp }
    have hL : (fun n => ρ (Multiplicative.ofAdd n) v) = L v := by
      funext n
      simp only [L, LinearMap.coe_mk, AddHom.coe_mk, ρ', T, MonoidHom.coe_comp,
        Function.comp_apply, ← map_zpow, Representation.asGroupHom_apply,
        ← Module.End.mul_apply, ← map_mul, ← ofAdd_eq_consZero_mul]
    rw [hL]
    have htop : ⊤ ≤ (space (d + 1) V).comap L := by
      rw [← Module.End.iSup_maxGenEigenspace_eq_top (T : Module.End ℂ V)]
      refine iSup_le fun μ => ?_
      intro w hw
      obtain ⟨K, hK⟩ := (Module.End.mem_maxGenEigenspace _ _ _).mp hw
      by_cases hμ : μ = 0
      · subst hμ
        have hw0 : w = 0 := by
          simp only [zero_smul, sub_zero] at hK
          have hinj : Function.Injective
              (((T ^ K : (Module.End ℂ V)ˣ) : Module.End ℂ V)) := by
            intro a b hab
            have h := congrArg ((((T ^ K)⁻¹ : (Module.End ℂ V)ˣ) : Module.End ℂ V)) hab
            simpa only [← Module.End.mul_apply, Units.inv_mul, Module.End.one_apply] using h
          apply hinj
          rw [Units.val_pow_eq_pow_val, hK, map_zero]
        rw [hw0, Submodule.mem_comap, map_zero]
        exact Submodule.zero_mem _
      · set M : Module.End ℂ V := μ⁻¹ • ((T : Module.End ℂ V) - μ • 1)
        have hLw : L w = ∑ k ∈ Finset.range (K + 1),
            (fun n : Fin (d + 1) → ℤ =>
              (((Units.mk0 μ hμ : ℂˣ) : ℂ) ^ (n 0) * binomCoeff k (n 0)) •
                (fun n' => ρ' (Multiplicative.ofAdd n') ((M ^ k) w)) (Fin.tail n)) := by
          funext n
          simp only [L, LinearMap.coe_mk, AddHom.coe_mk, Finset.sum_apply,
            zpow_apply_of_genEigen T hμ hK, Units.val_mk0, map_smul, map_sum, Finset.smul_sum,
            smul_smul, M]
        rw [Submodule.mem_comap, hLw]
        exact Submodule.sum_mem _ fun k _ => cons_mem _ k (ih ρ' _)
    exact htop Submodule.mem_top

end Langlands.IntegerLatticeExponentialPolynomial

namespace Langlands

open IntegerLatticeExponentialPolynomial

universe u

/-- Renard C.III: every matrix coefficient of a finite-dimensional complex representation of
`ℤ^d` is one finite sum of characters times polynomials on the whole integer lattice. -/
theorem integerLatticeMatrixCoefficientExponentialPolynomial :
    IntegerLatticeMatrixCoefficientExponentialPolynomialStatement.{u} := by
  intro d V _ _ _ ρ v ell
  obtain ⟨l, χ, Q, hQ⟩ := exists_of_mem (comp_mem ell (orbit_mem_space d ρ v))
  exact ⟨l, χ, Q, fun n => hQ n⟩

end Langlands
