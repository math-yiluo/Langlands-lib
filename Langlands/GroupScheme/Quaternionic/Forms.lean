import Langlands.GroupScheme.Quaternionic.Involution
import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.LinearAlgebra.Quotient.Basic
import Mathlib.Order.ConditionallyCompleteLattice.Basic

/-!
# Antihermitian and quadratic forms over an algebra with involution

Let `σ` be an involution of the first kind of a division algebra `D` over a field `K`.
On the left `D`-vector space `D^n` of row vectors, a matrix `H ∈ M_n(D)` defines the
sesquilinear form `h(x, y) = ∑ i j, x i * H i j * σ (y j)`. This module defines
nondegenerate trace-valued `σ`-antihermitian Gram matrices and their Witt index, and
Tits's `σ`-quadratic forms, the elements of `M_n(D) ⧸ {x - ᵗx^σ}`, with their polar
matrix, their values in `D ⧸ {a - σ a}`, nondegeneracy and Witt index.
-/

noncomputable section

universe u v w

namespace Langlands.GroupScheme.Quaternionic

namespace FirstKindInvolution

variable {K : Type u} {D : Type v} [Field K] [DivisionRing D] [Algebra K D]
  (σ : FirstKindInvolution K D) {n : Type w} [Fintype n] [DecidableEq n]

/-! ### Sesquilinear forms on row vectors -/

/-- The value `h(x, y) = ∑ i j, x i * H i j * σ (y j)` of the sesquilinear form with
Gram matrix `H` on row vectors `x y : n → D`. It is left `D`-linear in `x` and
`σ`-semilinear on the right in `y`: `h(a x, b y) = a h(x, y) σ(b)`. -/
def sesqForm (H : Matrix n n D) (x y : n → D) : D :=
  ∑ i, ∑ j, x i * H i j * σ (y j)

/-- Applying `σ` to `h(x, x)` gives the value at `x` of the form with Gram matrix
`ᵗH^σ`. -/
theorem map_sesqForm_self (H : Matrix n n D) (x : n → D) :
    σ (σ.sesqForm H x x) = σ.sesqForm (σ.matrix n H) x x := by
  simp only [sesqForm, map_sum, map_mul, apply_apply, matrix_apply, mul_assoc]
  exact Finset.sum_comm

/-- A Gram matrix `H` is (trace-valued) `σ`-antihermitian when `ᵗH^σ = -H`, that is
`h(y, x) = -σ (h(x, y))`, and every diagonal entry has the form `a - σ a`. The second
condition is automatic when `2` is invertible in `K`; in characteristic `2` it says that
`h(x, x) ∈ {a - σ a}` for every `x`. -/
def IsAntihermitian (H : Matrix n n D) : Prop :=
  σ.matrix n H = -H ∧ ∀ i, H i i ∈ σ.alternatingSubspace

/-- A left `D`-subspace `W` of `D^n` is totally isotropic for the form with Gram matrix
`H` when `h(x, y) = 0` for all `x y ∈ W`. -/
def IsTotallyIsotropic (H : Matrix n n D) (W : Submodule D (n → D)) : Prop :=
  ∀ x ∈ W, ∀ y ∈ W, σ.sesqForm H x y = 0

/-- The Witt index of the form with Gram matrix `H`: the largest `D`-dimension of a totally
isotropic subspace of `D^n`. -/
def wittIndex (H : Matrix n n D) : ℕ :=
  sSup {r | ∃ W : Submodule D (n → D), σ.IsTotallyIsotropic H W ∧ Module.finrank D W = r}

/-! ### Quadratic forms in the sense of Tits -/

variable (n) in
/-- Tits's subspace `T = {x - ᵗx^σ | x ∈ M_n(D)}` of the matrix algebra. -/
def quadraticKernel : Submodule K (Matrix n n D) := (σ.matrix n).alternatingSubspace

variable (n) in
/-- The `K`-vector space of `σ`-quadratic forms on `D^n` in the sense of Tits:
`M_n(D) ⧸ {x - ᵗx^σ}`. -/
abbrev QuadraticForms : Type _ := Matrix n n D ⧸ σ.quadraticKernel n

/-- The polar (hermitian) Gram matrix `Q + ᵗQ^σ` of the quadratic form with representative
`Q`; it does not depend on the representative. -/
def polar : σ.QuadraticForms n →ₗ[K] Matrix n n D :=
  (σ.quadraticKernel n).liftQ (LinearMap.id + (σ.matrix n).toLinearMap) (by
    rintro _ ⟨a, rfl⟩
    simp)

@[simp] theorem polar_mk (Q : Matrix n n D) :
    σ.polar (Submodule.Quotient.mk Q : σ.QuadraticForms n) = Q + σ.matrix n Q :=
  rfl

/-- For fixed `x`, the `K`-linear map `Q ↦ ∑ i j, x i * Q i j * σ (x j)`. -/
def evalLinear (x : n → D) : Matrix n n D →ₗ[K] D where
  toFun Q := σ.sesqForm Q x x
  map_add' Q Q' := by
    simp only [sesqForm, Matrix.add_apply, mul_add, add_mul, Finset.sum_add_distrib]
  map_smul' c Q := by
    simp only [sesqForm, Matrix.smul_apply, RingHom.id_apply, Finset.smul_sum,
      mul_smul_comm, smul_mul_assoc]

omit [DecidableEq n] in
@[simp] theorem evalLinear_apply (x : n → D) (Q : Matrix n n D) :
    σ.evalLinear x Q = σ.sesqForm Q x x :=
  rfl

/-- The value `q(x) ∈ D ⧸ {a - σ a}` of a quadratic form `q` at a row vector `x`: the class
of `∑ i j, x i * Q i j * σ (x j)` for any representative `Q` of `q`. -/
def quadraticValue (x : n → D) : σ.QuadraticForms n →ₗ[K] D ⧸ σ.alternatingSubspace :=
  (σ.quadraticKernel n).liftQ (σ.alternatingSubspace.mkQ ∘ₗ σ.evalLinear x) (by
    rintro _ ⟨a, rfl⟩
    rw [LinearMap.mem_ker, LinearMap.comp_apply, Submodule.mkQ_apply,
      Submodule.Quotient.mk_eq_zero, LinearMap.sub_apply, LinearMap.id_apply,
      LinearMap.map_sub, coe_toLinearMap, evalLinear_apply, evalLinear_apply,
      ← map_sesqForm_self]
    exact σ.sub_mem_alternatingSubspace _)

@[simp] theorem quadraticValue_mk (x : n → D) (Q : Matrix n n D) :
    σ.quadraticValue x (Submodule.Quotient.mk Q : σ.QuadraticForms n) =
      Submodule.Quotient.mk (σ.sesqForm Q x x) :=
  rfl

/-- A quadratic form is nondegenerate when its polar Gram matrix is invertible. -/
def IsNondegenerateQuadratic (q : σ.QuadraticForms n) : Prop :=
  IsUnit (σ.polar q)

/-- A left `D`-subspace `W` of `D^n` is totally singular for `q` when `q(x) = 0` for every
`x ∈ W`. -/
def IsTotallySingular (q : σ.QuadraticForms n) (W : Submodule D (n → D)) : Prop :=
  ∀ x ∈ W, σ.quadraticValue x q = 0

/-- The Witt index of a quadratic form: the largest `D`-dimension of a totally singular
subspace of `D^n`. -/
def quadraticWittIndex (q : σ.QuadraticForms n) : ℕ :=
  sSup {r | ∃ W : Submodule D (n → D), σ.IsTotallySingular q W ∧ Module.finrank D W = r}

end FirstKindInvolution

end Langlands.GroupScheme.Quaternionic
