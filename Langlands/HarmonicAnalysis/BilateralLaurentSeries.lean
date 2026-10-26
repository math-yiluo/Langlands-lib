import Mathlib.Algebra.Polynomial.Laurent
import Mathlib.MeasureTheory.Integral.Bochner.Basic

/-!
# Bilateral formal Laurent series and coefficientwise integration

Jacquet, Piatetski-Shapiro and Shalika, *Rankin-Selberg convolutions* (1983),
Section (4.1), printed page 406: formal Laurent series `∑ aₘ Xᵐ` with complex
coefficients over all `m ∈ ℤ`, their module structure over `ℂ[X, X⁻¹]`, and
coefficientwise integrability and integration of families of such series.
No support condition is imposed on the series.
-/

noncomputable section

open MeasureTheory LaurentPolynomial

namespace Langlands.HarmonicAnalysis

/-- JPSS (4.1)(1): a formal Laurent series `∑ aₘ Xᵐ` with complex coefficients, the
sum extended over all `m ∈ ℤ`, recorded by its coefficient function `m ↦ aₘ`. -/
def BilateralLaurentSeries : Type := ℤ → ℂ

namespace BilateralLaurentSeries

instance : AddCommGroup BilateralLaurentSeries := inferInstanceAs (AddCommGroup (ℤ → ℂ))

instance : Module ℂ BilateralLaurentSeries := inferInstanceAs (Module ℂ (ℤ → ℂ))

instance : Inhabited BilateralLaurentSeries := ⟨0⟩

@[ext]
theorem ext {a b : BilateralLaurentSeries} (h : ∀ n, a n = b n) : a = b :=
  funext h

@[simp] theorem zero_apply (n : ℤ) : (0 : BilateralLaurentSeries) n = 0 := rfl

@[simp] theorem add_apply (a b : BilateralLaurentSeries) (n : ℤ) :
    (a + b) n = a n + b n := rfl

@[simp] theorem neg_apply (a : BilateralLaurentSeries) (n : ℤ) : (-a) n = -a n := rfl

@[simp] theorem sub_apply (a b : BilateralLaurentSeries) (n : ℤ) :
    (a - b) n = a n - b n := rfl

@[simp] theorem smul_apply (c : ℂ) (a : BilateralLaurentSeries) (n : ℤ) :
    (c • a) n = c * a n := rfl

theorem sum_apply {ι : Type*} (s : Finset ι) (f : ι → BilateralLaurentSeries) (n : ℤ) :
    (∑ i ∈ s, f i) n = ∑ i ∈ s, f i n :=
  Finset.sum_apply n s f

/-! ### Multiplication by monomials -/

/-- Multiplication by `Xᵐ`: the coefficient at `n` of `Xᵐ · ∑ aₖ Xᵏ` is `a_{n - m}`. -/
def shift (m : ℤ) : BilateralLaurentSeries →ₗ[ℂ] BilateralLaurentSeries where
  toFun a := fun n => a (n - m)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

@[simp] theorem shift_apply (m : ℤ) (a : BilateralLaurentSeries) (n : ℤ) :
    shift m a n = a (n - m) := rfl

/-- The shifts form an action of the multiplicative group `{Xᵐ}`. -/
def shiftHom : Multiplicative ℤ →* Module.End ℂ BilateralLaurentSeries where
  toFun m := shift m.toAdd
  map_one' := by
    ext a n
    simp
  map_mul' j k := by
    ext a n
    simp [sub_sub]

@[simp] theorem shiftHom_apply (m : Multiplicative ℤ) :
    shiftHom m = shift m.toAdd := rfl

/-! ### The module over Laurent polynomials -/

/-- The `ℂ`-algebra map from Laurent polynomials sending `T m` to the shift by `m`. -/
def laurentAction : LaurentPolynomial ℂ →ₐ[ℂ] Module.End ℂ BilateralLaurentSeries :=
  AddMonoidAlgebra.lift ℂ (Module.End ℂ BilateralLaurentSeries) ℤ shiftHom

/-- JPSS (4.1): bilateral series form a module, with torsion, over `ℂ[X, X⁻¹]`. -/
instance instModuleLaurentPolynomial : Module (LaurentPolynomial ℂ) BilateralLaurentSeries :=
  Module.compHom BilateralLaurentSeries laurentAction.toRingHom

theorem laurent_smul_def (P : LaurentPolynomial ℂ) (a : BilateralLaurentSeries) :
    P • a = laurentAction P a := rfl

/-- The action of a Laurent polynomial is finite convolution of coefficients. -/
theorem laurent_smul_apply (P : LaurentPolynomial ℂ) (a : BilateralLaurentSeries) (n : ℤ) :
    (P • a) n = ∑ k ∈ P.coeff.support, P.coeff k * a (n - k) := by
  rw [laurent_smul_def, laurentAction, AddMonoidAlgebra.lift_apply, Finsupp.sum,
    LinearMap.sum_apply, sum_apply]
  simp

/-- Monomial evaluation law: `T m` shifts coefficients by `m`. -/
@[simp] theorem T_smul_apply (m : ℤ) (a : BilateralLaurentSeries) (n : ℤ) :
    ((T m : LaurentPolynomial ℂ) • a) n = a (n - m) := by
  rw [laurent_smul_def, laurentAction,
    show (T m : LaurentPolynomial ℂ) = AddMonoidAlgebra.single m 1 from rfl,
    AddMonoidAlgebra.lift_single]
  simp

/-- Constant Laurent polynomials act through complex scalar multiplication. -/
@[simp] theorem C_smul (c : ℂ) (a : BilateralLaurentSeries) :
    (C c : LaurentPolynomial ℂ) • a = c • a := by
  ext n
  rw [laurent_smul_def, laurentAction, ← single_eq_C, AddMonoidAlgebra.lift_single]
  simp

/-- Evaluation law for a general monomial `c Tᵐ`. -/
theorem C_mul_T_smul_apply (c : ℂ) (m : ℤ) (a : BilateralLaurentSeries) (n : ℤ) :
    ((C c * T m : LaurentPolynomial ℂ) • a) n = c * a (n - m) := by
  rw [mul_smul, C_smul, smul_apply, T_smul_apply]

instance : IsScalarTower ℂ (LaurentPolynomial ℂ) BilateralLaurentSeries where
  smul_assoc c P a := by
    rw [laurent_smul_def, laurent_smul_def, map_smul]
    rfl

instance : SMulCommClass ℂ (LaurentPolynomial ℂ) BilateralLaurentSeries where
  smul_comm c P a := by
    rw [laurent_smul_def, laurent_smul_def, map_smul]

/-- Torsion example: the series `∑ₘ Xᵐ`, all of whose coefficients are `1`, is
annihilated by `1 - X`. -/
theorem one_sub_T_one_smul_eq_zero (a : BilateralLaurentSeries) (ha : ∀ n, a n = 1) :
    (1 - T 1 : LaurentPolynomial ℂ) • a = 0 := by
  ext n
  rw [sub_smul, one_smul, sub_apply, T_smul_apply, ha, ha, sub_self, zero_apply]

/-! ### Laurent polynomials as bilateral series -/

/-- The coefficient function `n ↦ P.coeff n` of a Laurent polynomial. -/
def coeffSeries (P : LaurentPolynomial ℂ) : BilateralLaurentSeries := fun n => P.coeff n

/-- The coefficient function of a Laurent polynomial, as a map of
`LaurentPolynomial ℂ`-modules. -/
def ofLaurentPolynomial :
    LaurentPolynomial ℂ →ₗ[LaurentPolynomial ℂ] BilateralLaurentSeries where
  toFun := coeffSeries
  map_add' _ _ := rfl
  map_smul' P Q := by
    ext n
    rw [RingHom.id_apply, laurent_smul_apply, smul_eq_mul]
    change (P * Q).coeff n = ∑ k ∈ P.coeff.support, P.coeff k * Q.coeff (n - k)
    rw [AddMonoidAlgebra.coeff_mul_apply_left, Finsupp.sum]
    exact Finset.sum_congr rfl fun k _ => by rw [neg_add_eq_sub]

@[simp] theorem ofLaurentPolynomial_apply (P : LaurentPolynomial ℂ) (n : ℤ) :
    ofLaurentPolynomial P n = P.coeff n := rfl

theorem ofLaurentPolynomial_injective : Function.Injective ofLaurentPolynomial :=
  fun _ _ h => LaurentPolynomial.ext fun n => congrArg (fun a : BilateralLaurentSeries => a n) h

/-- Compatibility with the module action: products of Laurent polynomials are
computed by the action on bilateral series. -/
theorem ofLaurentPolynomial_mul (P Q : LaurentPolynomial ℂ) :
    ofLaurentPolynomial (P * Q) = P • ofLaurentPolynomial Q :=
  ofLaurentPolynomial.map_smul P Q

/-! ### One-sided support predicates -/

/-- The support `{n | aₙ ≠ 0}` is bounded below. -/
def HasLowerBoundedSupport (a : BilateralLaurentSeries) : Prop :=
  BddBelow {n : ℤ | a n ≠ 0}

/-- The support `{n | aₙ ≠ 0}` is bounded above. -/
def HasUpperBoundedSupport (a : BilateralLaurentSeries) : Prop :=
  BddAbove {n : ℤ | a n ≠ 0}

theorem hasLowerBoundedSupport_iff (a : BilateralLaurentSeries) :
    HasLowerBoundedSupport a ↔ ∃ N : ℤ, ∀ n, n < N → a n = 0 := by
  simp only [HasLowerBoundedSupport, bddBelow_def, Set.mem_ofPred_eq]
  exact exists_congr fun N => forall_congr' fun n => by rw [not_imp_comm, not_le]

theorem hasUpperBoundedSupport_iff (a : BilateralLaurentSeries) :
    HasUpperBoundedSupport a ↔ ∃ N : ℤ, ∀ n, N < n → a n = 0 := by
  simp only [HasUpperBoundedSupport, bddAbove_def, Set.mem_ofPred_eq]
  exact exists_congr fun N => forall_congr' fun n => by rw [not_imp_comm, not_le]

theorem hasLowerBoundedSupport_ofLaurentPolynomial (P : LaurentPolynomial ℂ) :
    HasLowerBoundedSupport (ofLaurentPolynomial P) := by
  have h : {n : ℤ | ofLaurentPolynomial P n ≠ 0} = ↑P.coeff.support := by
    ext n
    simp
  rw [HasLowerBoundedSupport, h]
  exact P.coeff.support.bddBelow

theorem hasUpperBoundedSupport_ofLaurentPolynomial (P : LaurentPolynomial ℂ) :
    HasUpperBoundedSupport (ofLaurentPolynomial P) := by
  have h : {n : ℤ | ofLaurentPolynomial P n ≠ 0} = ↑P.coeff.support := by
    ext n
    simp
  rw [HasUpperBoundedSupport, h]
  exact P.coeff.support.bddAbove

/-! ### Coefficientwise integration -/

variable {A : Type*} [MeasurableSpace A] {μ : Measure A} {s t : A → BilateralLaurentSeries}

/-- JPSS (4.1): a family `s(λ, X) = ∑ aₘ(λ) Xᵐ` is integrable if every
coefficient `aₘ` is integrable. -/
def CoeffwiseIntegrable (s : A → BilateralLaurentSeries) (μ : Measure A) : Prop :=
  ∀ n : ℤ, Integrable (fun x => s x n) μ

/-- JPSS (4.1): `∮ s(λ, X) dλ = ∑ Xᵐ ∫ aₘ(λ) dλ`, integrating every coefficient. -/
def coeffwiseIntegral (μ : Measure A) (s : A → BilateralLaurentSeries) :
    BilateralLaurentSeries :=
  fun n => ∫ x, s x n ∂μ

@[simp] theorem coeffwiseIntegral_apply (μ : Measure A) (s : A → BilateralLaurentSeries)
    (n : ℤ) : coeffwiseIntegral μ s n = ∫ x, s x n ∂μ := rfl

theorem CoeffwiseIntegrable.zero : CoeffwiseIntegrable (fun _ => (0 : BilateralLaurentSeries)) μ :=
  fun _ => integrable_zero _ _ _

theorem CoeffwiseIntegrable.add (hs : CoeffwiseIntegrable s μ) (ht : CoeffwiseIntegrable t μ) :
    CoeffwiseIntegrable (fun x => s x + t x) μ :=
  fun n => (hs n).add (ht n)

theorem CoeffwiseIntegrable.neg (hs : CoeffwiseIntegrable s μ) :
    CoeffwiseIntegrable (fun x => -s x) μ :=
  fun n => (hs n).neg

theorem CoeffwiseIntegrable.sub (hs : CoeffwiseIntegrable s μ) (ht : CoeffwiseIntegrable t μ) :
    CoeffwiseIntegrable (fun x => s x - t x) μ :=
  fun n => (hs n).sub (ht n)

theorem CoeffwiseIntegrable.smul (c : ℂ) (hs : CoeffwiseIntegrable s μ) :
    CoeffwiseIntegrable (fun x => c • s x) μ :=
  fun n => (hs n).const_mul c

/-- A fixed Laurent polynomial preserves coefficientwise integrability: each
coefficient of `P • s x` is a finite sum of integrable functions. -/
theorem CoeffwiseIntegrable.laurent_smul (P : LaurentPolynomial ℂ)
    (hs : CoeffwiseIntegrable s μ) : CoeffwiseIntegrable (fun x => P • s x) μ := by
  intro n
  simp only [laurent_smul_apply]
  exact integrable_finsetSum _ fun k _ => (hs (n - k)).const_mul (P.coeff k)

theorem coeffwiseIntegral_zero :
    coeffwiseIntegral μ (fun _ => (0 : BilateralLaurentSeries)) = 0 := by
  ext n
  simp only [coeffwiseIntegral_apply, zero_apply]
  exact integral_zero _ _

theorem coeffwiseIntegral_add (hs : CoeffwiseIntegrable s μ) (ht : CoeffwiseIntegrable t μ) :
    coeffwiseIntegral μ (fun x => s x + t x) = coeffwiseIntegral μ s + coeffwiseIntegral μ t := by
  ext n
  simp only [coeffwiseIntegral_apply, add_apply]
  exact integral_add (hs n) (ht n)

theorem coeffwiseIntegral_neg (s : A → BilateralLaurentSeries) :
    coeffwiseIntegral μ (fun x => -s x) = -coeffwiseIntegral μ s := by
  ext n
  simp only [coeffwiseIntegral_apply, neg_apply]
  exact integral_neg _

theorem coeffwiseIntegral_sub (hs : CoeffwiseIntegrable s μ) (ht : CoeffwiseIntegrable t μ) :
    coeffwiseIntegral μ (fun x => s x - t x) = coeffwiseIntegral μ s - coeffwiseIntegral μ t := by
  ext n
  simp only [coeffwiseIntegral_apply, sub_apply]
  exact integral_sub (hs n) (ht n)

theorem coeffwiseIntegral_smul (c : ℂ) (s : A → BilateralLaurentSeries) :
    coeffwiseIntegral μ (fun x => c • s x) = c • coeffwiseIntegral μ s := by
  ext n
  simp only [coeffwiseIntegral_apply, smul_apply]
  exact integral_const_mul c _

/-- JPSS (4.1): integration commutes with multiplication by a fixed Laurent
polynomial, by integrating the finite coefficient sums termwise. -/
theorem coeffwiseIntegral_laurent_smul (P : LaurentPolynomial ℂ)
    (hs : CoeffwiseIntegrable s μ) :
    coeffwiseIntegral μ (fun x => P • s x) = P • coeffwiseIntegral μ s := by
  ext n
  simp only [coeffwiseIntegral_apply, laurent_smul_apply]
  rw [integral_finsetSum _ fun k _ => (hs (n - k)).const_mul (P.coeff k)]
  exact Finset.sum_congr rfl fun k _ => integral_const_mul _ _

end BilateralLaurentSeries

end Langlands.HarmonicAnalysis
