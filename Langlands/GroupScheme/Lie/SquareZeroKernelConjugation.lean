import Langlands.GroupScheme.Lie.SquareZeroKernelAdditive
import Langlands.GroupScheme.Lie.ActionDifferential
import Mathlib.GroupTheory.GroupAction.ConjAct

/-! # Conjugation and evaluation in actual square-zero kernels -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj TensorProduct

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000

namespace Langlands.GroupScheme.Lie.SquareZero

variable {R : CommRingCat.{u}} (G : GroupScheme (Spec R))
variable {A : Type u} [CommRing A] [Algebra R A] (I : Ideal A)

/-- Actual point conjugation on the normal reduction kernel. -/
def kernelConjugation : AffinePoints G A →* MulAut (kernel G I) :=
  MulAut.conjNormal

@[simp]
theorem kernelConjugation_val (g : AffinePoints G A) (x : kernel G I) :
    (kernelConjugation G I g x).val = g * x.val * g⁻¹ :=
  MulAut.conjNormal_apply g x

variable [IsAffineHom G.X.hom]

/-- A square-zero kernel element acts trivially on the reduction kernel. -/
theorem kernelConjugation_of_kernel (hI : I ^ 2 = ⊥)
    (g x : kernel G I) : kernelConjugation G I g.val x = x := by
  apply Subtype.ext
  rw [kernelConjugation_val]
  have h := congrArg Subtype.val (kernel_mul_comm G I hI g x)
  change g.val * x.val = x.val * g.val at h
  rw [h, mul_inv_cancel_right]

/-- Conjugation on a square-zero kernel depends only on the reducing point,
with no surjectivity assumption on the reduction map. -/
theorem kernelConjugation_eq_of_reduction_eq (hI : I ^ 2 = ⊥)
    (g g' : AffinePoints G A) (h : reduction G I g = reduction G I g') :
    kernelConjugation G I g = kernelConjugation G I g' := by
  apply MulEquiv.ext
  intro x
  let d : kernel G I := ⟨g'⁻¹ * g, by
    change reduction G I (g'⁻¹ * g) = 1
    rw [map_mul, map_inv, h, inv_mul_cancel]⟩
  have hc := congrArg Subtype.val (kernel_mul_comm G I hI d x)
  change (g'⁻¹ * g) * x.val = x.val * (g'⁻¹ * g) at hc
  apply Subtype.ext
  simp only [kernelConjugation_val]
  have he := congrArg (fun z => g' * z * g⁻¹) hc
  simpa only [mul_assoc, mul_inv_cancel_left, inv_mul_cancel_left,
    mul_inv_cancel_right, mul_inv_cancel, mul_one] using he

attribute [local instance] coordinateOriginAlgebra

/-- Evaluate a dual-number infinitesimal in a specified actual ideal element. -/
def tangentEvaluation (hI : I ^ 2 = ⊥) (i : I) : DualNumber A →ₐ[R] A :=
  (collapse (R := R) I hI).comp
    (squareMap (LinearMap.toSpanSingleton A I i))

@[simp]
theorem tangentEvaluation_apply (hI : I ^ 2 = ⊥) (i : I) (z : DualNumber A) :
    tangentEvaluation (R := R) I hI i z = z.fst + z.snd * (i : A) := by
  simp only [tangentEvaluation, AlgHom.comp_apply, collapse_apply,
    squareMap_fst, squareMap_snd, LinearMap.toSpanSingleton_apply,
    Submodule.coe_smul_of_tower, Algebra.smul_def, Algebra.algebraMap_self, RingHom.id_apply]

omit [IsAffineHom G.X.hom] in
/-- Evaluation of a constant dual-number point is the original point. -/
theorem tangentEvaluation_constant (hI : I ^ 2 = ⊥) (i : I)
    (g : AffinePoints G A) :
    affineMap G (tangentEvaluation (R := R) I hI i) (constant G g) = g := by
  rw [constant, ← affineMap_comp]
  have he : (tangentEvaluation (R := R) I hI i).comp
      (TrivSqZeroExt.inlAlgHom R A A) = AlgHom.id R A := by
    apply AlgHom.ext
    intro a
    rw [AlgHom.comp_apply, tangentEvaluation_apply]
    change a + 0 * (i : A) = a
    simp
  rw [he, affineMap_id]

/-- A Lie tangent vector evaluated in an actual square-zero ideal lies in the
actual reduction kernel. -/
def tangentPoint (hI : I ^ 2 = ⊥) (i : I) : lieKernel G A →* kernel G I where
  toFun X := ⟨affineMap G (tangentEvaluation (R := R) I hI i) X.val, by
    change affineMap G (Ideal.Quotient.mkₐ R I)
      (affineMap G (tangentEvaluation (R := R) I hI i) X.val) = 1
    rw [← affineMap_comp]
    have he : (Ideal.Quotient.mkₐ R I).comp
        (tangentEvaluation (R := R) I hI i) =
        (Ideal.Quotient.mkₐ R I).comp (TrivSqZeroExt.fstHom R A A) := by
      apply AlgHom.ext
      intro z
      rw [AlgHom.comp_apply, tangentEvaluation_apply]
      change Ideal.Quotient.mk I (z.fst + z.snd * (i : A)) =
        Ideal.Quotient.mk I z.fst
      rw [map_add, map_mul, Ideal.Quotient.eq_zero_iff_mem.mpr i.property,
        mul_zero, add_zero]
    rw [he, affineMap_comp]
    change affineMap G (Ideal.Quotient.mkₐ R I) (Lie.reduction G X.val) = 1
    rw [X.property, map_one]⟩
  map_one' := Subtype.ext (map_one _)
  map_mul' X Y := Subtype.ext (map_mul _ X.val Y.val)

omit [IsAffineHom G.X.hom] in
@[simp]
theorem tangentPoint_val (hI : I ^ 2 = ⊥) (i : I) (X : lieKernel G A) :
    (tangentPoint G I hI i X).val =
      affineMap G (tangentEvaluation (R := R) I hI i) X.val := rfl

/-- Its ideal-valued derivation is the Lie derivation multiplied by the
specified ideal element. -/
theorem tangentPoint_derivation (hI : I ^ 2 = ⊥) (i : I) (X : lieKernel G A)
    (b : coordinateAlgebra G) :
    (kernelDerivationEquiv G I hI (tangentPoint G I hI i X) b : A) =
      Lie.kernelDerivationEquiv G X b * (i : A) := by
  rw [kernelDerivationEquiv_apply, tangentPoint_val, pointCoordinates_naturality]
  rw [AlgHom.comp_apply, tangentEvaluation_apply]
  change (pointCoordinates G X.val b).fst +
      (pointCoordinates G X.val b).snd * (i : A) -
      algebraMap (coordinateAlgebra G) A b = _
  have hf := DFunLike.congr_fun (pointCoordinates_kernel G X) b
  change (pointCoordinates G X.val b).fst =
    algebraMap (coordinateAlgebra G) A b at hf
  rw [hf]
  change _ = (pointCoordinates G X.val b).snd * (i : A)
  abel

/-- Evaluating the actual adjoint tangent vector is conjugation of the
corresponding actual square-zero kernel point. -/
theorem tangentPoint_adjoint (hI : I ^ 2 = ⊥) (i : I)
    (g : AffinePoints G A) (X : Additive (lieKernel G A)) :
    tangentPoint G I hI i (adjoint G A g X).toMul =
      kernelConjugation G I g (tangentPoint G I hI i X.toMul) := by
  apply Subtype.ext
  simp only [tangentPoint_val, adjoint_val, map_mul, map_inv,
    tangentEvaluation_constant, kernelConjugation_val]

end Langlands.GroupScheme.Lie.SquareZero
