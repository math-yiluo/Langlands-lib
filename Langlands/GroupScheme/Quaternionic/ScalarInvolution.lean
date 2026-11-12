import Langlands.GroupScheme.Quaternionic.Forms

/-!
# The scalar involution

For a commutative ring `K`, the identity map of `K` is an involution of the first kind of
`K` regarded as a `K`-algebra. With this involution the constructions of
`Langlands.GroupScheme.Quaternionic.Forms` specialise to ordinary bilinear and quadratic
forms: the conjugate transpose is the plain transpose, the quadratic kernel is
`{x - ᵗx}`, the polar Gram matrix of the class of `Q` is `Q + ᵗQ`, and the value of the
class of `Q` at a row vector `x` is the class of `∑ i j, x i * Q i j * x j` in `K ⧸ ⊥`.
-/

noncomputable section

universe u w

namespace Langlands.GroupScheme.Quaternionic

namespace FirstKindInvolution

section CommRing

variable (K : Type u) [CommRing K]

/-- The scalar involution: the identity map of a commutative ring `K`, an involution of the
first kind of `K` regarded as a `K`-algebra. -/
def scalar : FirstKindInvolution K K where
  toLinearMap := LinearMap.id
  map_one' := rfl
  map_mul' := fun x y => mul_comm x y
  involutive' := fun _ => rfl

variable {K}

@[simp] theorem scalar_apply (x : K) : scalar K x = x :=
  rfl

@[simp] theorem scalar_toLinearMap : (scalar K).toLinearMap = LinearMap.id :=
  rfl

/-- Every element is symmetric for the scalar involution. -/
@[simp] theorem symmetricSubspace_scalar : (scalar K).symmetricSubspace = ⊤ :=
  eq_top_iff.2 fun _ _ => (scalar K).mem_symmetricSubspace.2 rfl

/-- The only alternating element for the scalar involution is `0`. -/
@[simp] theorem alternatingSubspace_scalar : (scalar K).alternatingSubspace = ⊥ :=
  eq_bot_iff.2 fun x hx => by
    obtain ⟨a, rfl⟩ := (scalar K).mem_alternatingSubspace.1 hx
    simp

variable {n : Type w} [Fintype n] [DecidableEq n]

/-- The conjugate transpose for the scalar involution is the ordinary transpose. -/
@[simp] theorem scalar_matrix_apply (x : Matrix n n K) : (scalar K).matrix n x = x.transpose :=
  rfl

end CommRing

section Field

variable {K : Type u} [Field K] {n : Type w} [Fintype n] [DecidableEq n]

omit [DecidableEq n] in
/-- The sesquilinear form of the scalar involution with Gram matrix `H` is the ordinary
bilinear form `(x, y) ↦ ∑ i j, x i * H i j * y j`. -/
@[simp] theorem scalar_sesqForm (H : Matrix n n K) (x y : n → K) :
    (scalar K).sesqForm H x y = ∑ i, ∑ j, x i * H i j * y j :=
  rfl

/-- A matrix lies in the quadratic kernel of the scalar involution exactly when it has the
form `a - ᵗa`. -/
theorem mem_quadraticKernel_scalar (x : Matrix n n K) :
    x ∈ (scalar K).quadraticKernel n ↔ ∃ a : Matrix n n K, a - a.transpose = x :=
  (scalar K |>.matrix n).mem_alternatingSubspace

/-- The polar Gram matrix of the scalar quadratic form represented by `Q` is `Q + ᵗQ`. -/
@[simp] theorem scalar_polar_mk (Q : Matrix n n K) :
    (scalar K).polar (Submodule.Quotient.mk Q : (scalar K).QuadraticForms n) =
      Q + Q.transpose :=
  rfl

/-- A scalar quadratic form represented by `Q` is nondegenerate exactly when `Q + ᵗQ` is
invertible. -/
theorem isNondegenerateQuadratic_scalar_mk_iff (Q : Matrix n n K) :
    (scalar K).IsNondegenerateQuadratic
        (Submodule.Quotient.mk Q : (scalar K).QuadraticForms n) ↔
      IsUnit (Q + Q.transpose) :=
  Iff.rfl

/-- The value at `x` of the scalar quadratic form represented by `Q` vanishes exactly when
the ordinary quadratic form `∑ i j, x i * Q i j * x j` vanishes. -/
theorem scalar_quadraticValue_mk_eq_zero_iff (x : n → K) (Q : Matrix n n K) :
    (scalar K).quadraticValue x (Submodule.Quotient.mk Q : (scalar K).QuadraticForms n) = 0 ↔
      ∑ i, ∑ j, x i * Q i j * x j = 0 := by
  rw [quadraticValue_mk, Submodule.Quotient.mk_eq_zero, alternatingSubspace_scalar,
    Submodule.mem_bot, scalar_sesqForm]

end Field

end FirstKindInvolution

end Langlands.GroupScheme.Quaternionic
