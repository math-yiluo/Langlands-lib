import Langlands.LinearAlgebra.QuadraticReflectionGeneration
import Mathlib.LinearAlgebra.CliffordAlgebra.Conjugation
import Mathlib.LinearAlgebra.CliffordAlgebra.Inversion

/-! # Clifford units of quadratic reflection words -/

noncomputable section

universe u v

namespace Langlands.QuadraticForm

open QuadraticMap CliffordAlgebra

variable {F : Type u} {V : Type v} [Field F] [AddCommGroup V] [Module F V]
  (Q : QuadraticForm F V)

/-- Multiplication by the Clifford vector of a nonisotropic vector is invertible. -/
def cliffordVectorUnit (x : {x : V // Q x ≠ 0}) : (CliffordAlgebra Q)ˣ :=
  (isUnit_ι_of_isUnit Q (isUnit_iff_ne_zero.mpr x.property)).unit

@[simp] theorem cliffordVectorUnit_val (x : {x : V // Q x ≠ 0}) :
    (cliffordVectorUnit Q x : CliffordAlgebra Q) = ι Q (x : V) :=
  IsUnit.unit_spec _

/-- The Clifford product with its factors ordered to act by the reflections in list order. -/
def cliffordReflectionWord (l : List {x : V // Q x ≠ 0}) : (CliffordAlgebra Q)ˣ :=
  l.foldr (fun x w => w * cliffordVectorUnit Q x) 1

/-- The scalar obtained by multiplying a Clifford reflection word with its reversion. -/
theorem reverse_mul_cliffordReflectionWord (l : List {x : V // Q x ≠ 0}) :
    reverse (cliffordReflectionWord Q l : CliffordAlgebra Q) *
        (cliffordReflectionWord Q l : CliffordAlgebra Q) =
      algebraMap F (CliffordAlgebra Q)
        (l.map (fun x : {x : V // Q x ≠ 0} => Q x)).prod := by
  induction l with
  | nil => simp [cliffordReflectionWord]
  | cons x l ih =>
    let c : CliffordAlgebra Q := cliffordReflectionWord Q l
    let a : CliffordAlgebra Q := cliffordVectorUnit Q x
    change reverse (c * a) * (c * a) = _
    have ha : a = ι Q (x : V) := cliffordVectorUnit_val Q x
    rw [ha, reverse.map_mul, reverse_ι]
    calc
      (ι Q x * reverse c) * (c * ι Q x) =
          (ι Q x * (reverse c * c)) * ι Q x := by simp only [mul_assoc]
      _ = algebraMap F (CliffordAlgebra Q) ((x :: l).map
          (fun y : {y : V // Q y ≠ 0} => Q y)).prod := by
        rw [show reverse c * c = _ from ih, ← Algebra.commutes, mul_assoc, ι_sq_scalar,
          ← map_mul, List.map_cons, List.prod_cons, mul_comm]

private theorem cliffordVectorUnit_conj (x : {x : V // Q x ≠ 0}) (v : V) :
    (cliffordVectorUnit Q x : CliffordAlgebra Q) * ι Q v *
        ↑((cliffordVectorUnit Q x)⁻¹) = -ι Q (reflection Q x x.property v) := by
  let U := cliffordVectorUnit Q x
  apply (Units.mul_left_inj U).mp
  change (↑U * ι Q v * ↑U⁻¹) * ↑U = (-ι Q (reflection Q x x.property v)) * ↑U
  rw [mul_assoc (↑U * ι Q v), Units.inv_mul, mul_one,
    show (U : CliffordAlgebra Q) = ι Q (x : V) from cliffordVectorUnit_val Q x,
    reflection_apply, map_sub, map_smul, neg_sub, sub_mul, smul_mul_assoc, ι_sq_scalar,
    Algebra.smul_def, ← (algebraMap F (CliffordAlgebra Q)).map_mul,
    div_mul_cancel₀ _ x.property]
  rw [polar_comm]
  exact ι_mul_ι_comm _ _

/-- The signed conjugation by the Clifford word agrees with the product of reflections. -/
theorem cliffordReflectionWord_conj (l : List {x : V // Q x ≠ 0}) (v : V) :
    (cliffordReflectionWord Q l : CliffordAlgebra Q) * ι Q v *
        ↑((cliffordReflectionWord Q l)⁻¹) =
      ((-1 : F) ^ l.length) • ι Q (reflectionWord Q l v) := by
  induction l generalizing v with
  | nil =>
    change (1 : CliffordAlgebra Q) * ι Q v * 1 = (-1 : F) ^ 0 • ι Q v
    simp
  | cons x l ih =>
    let c := cliffordReflectionWord Q l
    let a := cliffordVectorUnit Q x
    change (↑c * ↑a) * ι Q v * ↑((c * a)⁻¹) = _
    rw [mul_inv_rev, Units.val_mul]
    calc
      (↑c * ↑a) * ι Q v * (↑a⁻¹ * ↑c⁻¹) =
          (↑c * ((↑a : CliffordAlgebra Q) * ι Q v * ↑a⁻¹)) * ↑c⁻¹ := by
        simp only [mul_assoc]
      _ = _ := by
        rw [show (↑a : CliffordAlgebra Q) * ι Q v * ↑a⁻¹ = _ from
          cliffordVectorUnit_conj Q x v, mul_neg, neg_mul, ih, List.length_cons, pow_succ,
          mul_neg_one, neg_smul]
        rfl

/-- For an even reflection word ordinary Clifford conjugation induces the stated isometry. -/
theorem cliffordReflectionWord_conj_of_even (l : List {x : V // Q x ≠ 0})
    (hl : Even l.length) (v : V) :
    (cliffordReflectionWord Q l : CliffordAlgebra Q) * ι Q v *
        ↑((cliffordReflectionWord Q l)⁻¹) = ι Q (reflectionWord Q l v) := by
  rw [cliffordReflectionWord_conj, hl.neg_one_pow, one_smul]

end Langlands.QuadraticForm
