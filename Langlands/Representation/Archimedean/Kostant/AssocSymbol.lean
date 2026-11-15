import Mathlib.Algebra.MvPolynomial.Derivation
import Mathlib.RingTheory.Derivation.Lie
import Langlands.Representation.Archimedean.Kostant.OrderedMonomials

/-!
# Symbol data for an associative algebra with a finite basis

Let `A` be a unital associative `K`-algebra with a basis `b` indexed by a finite type `B`, viewed
as a Lie algebra under the commutator. Put `S = K[X_c]` and `R = S[x_c]`, polynomials in the
coordinates `x_c` of a point `x = ∑ x_c b_c` of `A`. Right multiplication gives the derivations
`ρ(a) x_c = (x · a)_c = ∑_d x_d (b_d a)_c` of `R` over `S`, and `a ↦ ρ(a)` is a Lie algebra
map. With `𝔪` the ideal of the point `x = 1`, `ε` the evaluation at `x = 1` and
`l = ∑_c X_c (x_c - 1_c)`, the linear symbol is `ξ(a) = ε(ρ(a) l) = ∑_c a_c X_c`, so that
`ξ(b_c) = X_c`.
-/

noncomputable section

set_option autoImplicit false

namespace Langlands.Archimedean.Kostant

attribute [local instance 100] LieRing.ofAssociativeRing

open MvPolynomial

variable (K : Type*) [Field K] (A : Type*) [Ring A] [Algebra K A]
  {B : Type*} [Fintype B] [DecidableEq B] (b : Module.Basis B K A)

namespace AssocSymbol

/-- The symbol ring `K[X_c]`. -/
abbrev SymRing := MvPolynomial B K

/-- The coordinate ring `S[x_c]`. -/
abbrev CoordRing := MvPolynomial B (SymRing K (B := B))

variable {K A}

/-- The structure constants of right multiplication: `(b_d a)_c`. -/
def coeffMul (a : A) (d c : B) : K := b.repr (b d * a) c

omit [DecidableEq B] in
theorem sum_coeffMul_mul (f c : B) (a a' : A) :
    ∑ d, b.repr (b f * a) d * coeffMul b a' d c = b.repr (b f * a * a') c := by
  conv_rhs => rw [← b.sum_repr (b f * a), Finset.sum_mul]
  simp only [smul_mul_assoc, map_sum, map_smul, Finsupp.coe_finsetSum, Finset.sum_apply,
    Finsupp.smul_apply, smul_eq_mul, coeffMul]

omit [DecidableEq B] in
theorem sum_one_mul (c : B) (a : A) :
    ∑ d, b.repr 1 d * coeffMul b a d c = b.repr a c := by
  conv_rhs => rw [← one_mul a, ← b.sum_repr 1, Finset.sum_mul]
  simp only [smul_mul_assoc, map_sum, map_smul, Finsupp.coe_finsetSum, Finset.sum_apply,
    Finsupp.smul_apply, smul_eq_mul, coeffMul]

/-- The vector field of right multiplication by `a`, on the coordinates. -/
def field (a : A) (c : B) : CoordRing K (B := B) :=
  ∑ d, coeffMul b a d c • X d

/-- The derivation `ρ(a)` of right multiplication by `a`. -/
def der (a : A) : Derivation (SymRing K (B := B)) (CoordRing K (B := B)) (CoordRing K (B := B)) :=
  mkDerivation (SymRing K (B := B)) (field b a)

omit [DecidableEq B] in
theorem der_X (a : A) (c : B) : der b a (X c) = field b a c := mkDerivation_X _ _ _

omit [DecidableEq B] in
theorem der_C (a : A) (s : SymRing K (B := B)) : der b a (C s) = 0 :=
  (der b a).map_algebraMap s

omit [DecidableEq B] in
theorem der_smul_apply (a : A) (t : K) (f : CoordRing K (B := B)) :
    der b a (t • f) = t • der b a f :=
  (der b a).map_smul_of_tower t f

omit [DecidableEq B] in
theorem der_add (a a' : A) : der b (a + a') = der b a + der b a' := by
  apply MvPolynomial.derivation_ext
  intro c
  simp only [Derivation.add_apply, der_X, field, coeffMul, mul_add, map_add, Finsupp.add_apply,
    add_smul, Finset.sum_add_distrib]

omit [DecidableEq B] in
theorem der_smul (t : K) (a : A) : der b (t • a) = t • der b a := by
  apply MvPolynomial.derivation_ext
  intro c
  rw [Derivation.smul_apply, der_X, der_X]
  simp only [field, coeffMul, mul_smul_comm, map_smul, Finsupp.smul_apply, smul_eq_mul,
    Finset.smul_sum, mul_smul]

omit [DecidableEq B] in
theorem der_field (x y : A) (c : B) :
    der b x (field b y c) = ∑ f, b.repr (b f * x * y) c • (X f : CoordRing K (B := B)) := by
  simp only [field, map_sum, der_smul_apply, der_X, Finset.smul_sum, smul_smul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun f _ => ?_
  rw [← Finset.sum_smul, ← sum_coeffMul_mul b f c x y]
  simp only [coeffMul, mul_comm]

omit [DecidableEq B] in
theorem der_lie (a a' : A) : der b ⁅a, a'⁆ = ⁅der b a, der b a'⁆ := by
  apply MvPolynomial.derivation_ext
  intro c
  rw [Derivation.commutator_apply, der_X, der_X, der_X, der_field, der_field,
    ← Finset.sum_sub_distrib]
  simp only [field, coeffMul, Ring.lie_def, mul_sub, map_sub, ← mul_assoc, Finsupp.sub_apply,
    sub_smul]

/-- The representation of `A` by right-multiplication derivations, as a Lie algebra map. -/
def rho : A →ₗ⁅K⁆ Module.End K (CoordRing K (B := B)) where
  toFun a := ((der b a).toLinearMap).restrictScalars K
  map_add' a a' := by
    refine LinearMap.ext fun f => ?_
    change der b (a + a') f = der b a f + der b a' f
    rw [der_add]
    rfl
  map_smul' t a := by
    refine LinearMap.ext fun f => ?_
    change der b (t • a) f = t • der b a f
    rw [der_smul]
    rfl
  map_lie' {a a'} := by
    rw [Ring.lie_def (((der b a).toLinearMap).restrictScalars K)]
    refine LinearMap.ext fun f => ?_
    change der b ⁅a, a'⁆ f = der b a (der b a' f) - der b a' (der b a f)
    rw [der_lie, Derivation.commutator_apply]

omit [DecidableEq B] in
theorem rho_apply (a : A) (f : CoordRing K (B := B)) : rho b a f = der b a f := rfl

/-- The coordinates of the unit. -/
def one (c : B) : SymRing K (B := B) := algebraMap K _ (b.repr 1 c)

/-- The ideal of the unit point. -/
def ideal : Ideal (CoordRing K (B := B)) := Ideal.span (Set.range fun c => X c - C (one b c))

/-- Evaluation at the unit point. -/
def eval1 : CoordRing K (B := B) →ₐ[K] SymRing K (B := B) :=
  (aeval (one b)).restrictScalars K

omit [Fintype B] [DecidableEq B] in
theorem eval1_X (c : B) : eval1 b (X c) = one b c := by simp [eval1]

omit [Fintype B] [DecidableEq B] in
theorem eval1_C (s : SymRing K (B := B)) : eval1 b (C s) = s := by simp [eval1]

omit [Fintype B] [DecidableEq B] in
theorem eval1_eq_zero (f : CoordRing K (B := B)) (hf : f ∈ ideal b) : eval1 b f = 0 := by
  refine Submodule.span_induction ?_ ?_ ?_ ?_ hf
  · rintro _ ⟨c, rfl⟩
    simp [eval1_X, eval1_C]
  · simp
  · intro x y _ _ hx hy; simp [hx, hy]
  · intro s x _ hx
    rw [smul_eq_mul, map_mul, hx, mul_zero]

/-- The element `l = ∑_c X_c (x_c - 1_c)`. -/
def lin : CoordRing K (B := B) := ∑ c, C (X c) * (X c - C (one b c))

omit [DecidableEq B] in
theorem lin_mem : lin b ∈ ideal b :=
  Submodule.sum_mem _ fun c _ => Ideal.mul_mem_left _ _ (Ideal.subset_span ⟨c, rfl⟩)

variable [CharZero K]

/-- The symbol data of `A`. -/
def symbolData : SymbolData K A (CoordRing K (B := B)) (SymRing K (B := B)) where
  ρ := rho b
  leibniz a f g := by
    rw [rho_apply, rho_apply, rho_apply, Derivation.leibniz, smul_eq_mul, smul_eq_mul]
    ring
  𝔪 := ideal b
  ε := eval1 b
  ε_eq_zero := eval1_eq_zero b
  l := lin b
  l_mem := lin_mem b

omit [DecidableEq B] [CharZero K] in
theorem symbolData_ξ (a : A) :
    (symbolData b).ξ a = ∑ c, b.repr a c • (X c : SymRing K (B := B)) := by
  rw [SymbolData.ξ_apply]
  change eval1 b (der b a (lin b)) = _
  simp only [lin, map_sum, Derivation.leibniz, der_C, map_sub, der_X, smul_eq_mul, mul_zero,
    add_zero, sub_zero]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [map_mul, eval1_C, field, map_sum]
  simp only [map_smul, eval1_X]
  have h : ∀ d, coeffMul b a d c • one b d =
      algebraMap K (SymRing K (B := B)) (b.repr 1 d * coeffMul b a d c) := by
    intro d; rw [one, Algebra.smul_def, ← map_mul, mul_comm]
  rw [Finset.sum_congr rfl fun d _ => h d, ← map_sum, sum_one_mul, Algebra.smul_def, mul_comm]

theorem symbolData_ξ_basis (c : B) : (symbolData b).ξ (b c) = X c := by
  rw [symbolData_ξ]
  simp [Module.Basis.repr_self, Finsupp.single_apply]

end AssocSymbol

end Langlands.Archimedean.Kostant
