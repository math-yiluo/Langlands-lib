import Langlands.Representation.Tensor.UnitaryProof

/-!
# Positive rescaling and tensor products of invariant Hermitian forms

The published binary tensor core supplies positivity. This adapter equips the
original algebraic tensor with its actual external action and scaling laws.
-/

noncomputable section

open scoped TensorProduct ComplexConjugate

namespace Langlands.InvariantPositiveForm

universe uG uH uV uW

variable {G : Type uG} [Group G]
  {H : Type uH} [Group H]
  {V : Type uV} [AddCommGroup V] [Module ℂ V]
  {W : Type uW} [AddCommGroup W] [Module ℂ W]
  {ρ : Representation ℂ G V} {σ : Representation ℂ H W}

/-- An invariant positive form is determined by its inner products. -/
@[ext]
theorem ext_inner {b c : InvariantPositiveForm ρ}
    (h : ∀ v w, b.inner v w = c.inner v w) : b = c := by
  rcases b with ⟨⟨⟨⟨bi⟩, _, _, _, _⟩, _⟩, _⟩
  rcases c with ⟨⟨⟨⟨ci⟩, _, _, _, _⟩, _⟩, _⟩
  have hi : bi = ci := funext fun v => funext fun w => h v w
  cases hi
  rfl

/-- Additivity in the second variable, obtained from Hermitian symmetry. -/
theorem add_right (b : InvariantPositiveForm ρ) (v w z : V) :
    b.inner v (w + z) = b.inner v w + b.inner v z :=
  FiniteTensor.InvariantPositiveFormProof.core_inner_add_right b.toInnerProductCore v w z

/-- Multiply an invariant positive form by a strictly positive real scalar. -/
def rescale (b : InvariantPositiveForm ρ) (a : ℝ) (ha : 0 < a) :
    InvariantPositiveForm ρ where
  inner v w := (a : ℂ) * b.inner v w
  conj_inner_symm v w := by
    rw [map_mul, Complex.conj_ofReal, b.conj_inner_symm]
  re_inner_nonneg v := by
    change 0 ≤ ((a : ℂ) * b.inner v v).re
    rw [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
    exact mul_nonneg ha.le (b.re_inner_nonneg v)
  add_left v w z := by rw [b.add_left, mul_add]
  smul_left v w c := by rw [b.smul_left]; ring
  definite v hv := b.definite v
    ((mul_eq_zero.mp hv).resolve_left (Complex.ofReal_ne_zero.mpr ha.ne'))
  invariant g v w := by rw [b.invariant]

@[simp]
theorem rescale_inner (b : InvariantPositiveForm ρ) (a : ℝ) (ha : 0 < a)
    (v w : V) : (b.rescale a ha).inner v w = (a : ℂ) * b.inner v w := rfl

/-- The positive form on the original algebraic tensor, for the actual external
product action. No norm or topology is imposed on either original carrier. -/
def tensorProduct (b : InvariantPositiveForm ρ) (c : InvariantPositiveForm σ) :
    InvariantPositiveForm
      (Representation.tprod (ρ.comp (MonoidHom.fst G H))
        (σ.comp (MonoidHom.snd G H))) := by
  let C := Classical.choose
    (FiniteTensor.InvariantPositiveFormProof.exists_core_tmul
      b.toInnerProductCore c.toInnerProductCore)
  have hC := Classical.choose_spec
    (FiniteTensor.InvariantPositiveFormProof.exists_core_tmul
      b.toInnerProductCore c.toInnerProductCore)
  refine { toInnerProductCore := C, invariant := ?_ }
  intro x t s
  induction t using TensorProduct.inductionOn with
  | tmul v w =>
    induction s using TensorProduct.inductionOn with
    | tmul v' w' =>
      change C.inner (ρ x.1 v ⊗ₜ[ℂ] σ x.2 w) (ρ x.1 v' ⊗ₜ[ℂ] σ x.2 w') = _
      rw [hC, hC, b.invariant, c.invariant]
    | add s s' hs hs' =>
      simp only [map_add, FiniteTensor.InvariantPositiveFormProof.core_inner_add_right,
        hs, hs']
  | add t t' ht ht' =>
    simp only [map_add, C.add_left, ht, ht']

@[simp]
theorem tensorProduct_inner_tmul (b : InvariantPositiveForm ρ)
    (c : InvariantPositiveForm σ) (v v' : V) (w w' : W) :
    (b.tensorProduct c).inner (v ⊗ₜ[ℂ] w) (v' ⊗ₜ[ℂ] w') =
      b.inner v v' * c.inner w w' := by
  exact Classical.choose_spec
    (FiniteTensor.InvariantPositiveFormProof.exists_core_tmul
      b.toInnerProductCore c.toInnerProductCore) v v' w w'

/-- Rescaling the two factors multiplies every tensor pairing by the product
of the two positive real scalars. -/
theorem tensorProduct_rescale_inner (b : InvariantPositiveForm ρ)
    (c : InvariantPositiveForm σ) (a d : ℝ) (ha : 0 < a) (hd : 0 < d)
    (t s : V ⊗[ℂ] W) :
    ((b.rescale a ha).tensorProduct (c.rescale d hd)).inner t s =
      ((a * d : ℝ) : ℂ) * (b.tensorProduct c).inner t s := by
  induction t using TensorProduct.inductionOn with
  | tmul v w =>
    induction s using TensorProduct.inductionOn with
    | tmul v' w' =>
      simp only [tensorProduct_inner_tmul, rescale_inner, Complex.ofReal_mul]
      ring
    | add s s' hs hs' =>
      simp only [add_right, hs, hs', mul_add]
  | add t t' ht ht' =>
    simp only [PreInnerProductSpace.Core.add_left, ht, ht', mul_add]

/-- The two rescalings can equivalently be applied after taking the tensor form. -/
theorem tensorProduct_rescale (b : InvariantPositiveForm ρ)
    (c : InvariantPositiveForm σ) (a d : ℝ) (ha : 0 < a) (hd : 0 < d) :
    (b.rescale a ha).tensorProduct (c.rescale d hd) =
      (b.tensorProduct c).rescale (a * d) (mul_pos ha hd) := by
  apply ext_inner
  exact b.tensorProduct_rescale_inner c a d ha hd

/-- Reciprocal changes of the two forms cancel on the entire algebraic tensor. -/
theorem tensorProduct_rescale_inv (b : InvariantPositiveForm ρ)
    (c : InvariantPositiveForm σ) (a : ℝ) (ha : 0 < a) :
    (b.rescale a ha).tensorProduct (c.rescale a⁻¹ (inv_pos.mpr ha)) =
      b.tensorProduct c := by
  apply ext_inner
  intro t s
  rw [tensorProduct_rescale_inner, mul_inv_cancel₀ ha.ne', Complex.ofReal_one, one_mul]

end Langlands.InvariantPositiveForm
