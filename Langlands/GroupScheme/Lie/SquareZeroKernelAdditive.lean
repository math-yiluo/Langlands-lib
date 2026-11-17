import Langlands.GroupScheme.Lie.SquareZeroKernel

/-! # Multiplication in affine square-zero kernels is addition of derivations -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj TensorProduct

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000

namespace Langlands.GroupScheme.Lie.SquareZero

variable {R : CommRingCat.{u}} (G : GroupScheme (Spec R)) [IsAffineHom G.X.hom]
variable {A : Type u} [CommRing A] [Algebra R A] (I : Ideal A)

attribute [local instance] coordinateOriginAlgebra

/-- An ideal-valued augmentation derivation defines a point over the formal
split square-zero extension by that ideal. -/
def idealDerivationLift (d : Derivation R (coordinateAlgebra G) I) :
    coordinateAlgebra G →ₐ[R] TrivSqZeroExt A I where
  toFun b := ⟨algebraMap (coordinateAlgebra G) A b, d b⟩
  map_zero' := by ext <;> simp
  map_one' := by ext <;> simp
  map_add' b c := by
    apply TrivSqZeroExt.ext
    · exact map_add _ b c
    · exact map_add d b c
  map_mul' b c := by
    apply TrivSqZeroExt.ext
    · exact map_mul _ b c
    · apply Subtype.ext
      change (d (b * c) : A) =
        algebraMap (coordinateAlgebra G) A b * (d c : A) +
          (d b : A) * algebraMap (coordinateAlgebra G) A c
      have hd := congrArg (fun x : I => (x : A)) (d.leibniz b c)
      simpa only [Submodule.coe_add, Submodule.coe_smul_of_tower,
        Algebra.smul_def, mul_comm] using hd
  commutes' r := by
    apply TrivSqZeroExt.ext
    · exact (IsScalarTower.algebraMap_apply R (coordinateAlgebra G) A r).symm
    · exact d.map_algebraMap r

/-- The formal point with the derivation of the specified actual kernel point. -/
def formalPoint (hI : I ^ 2 = ⊥) (x : kernel G I) :
    AffinePoints G (TrivSqZeroExt A I) :=
  (pointCoordinates G).symm (idealDerivationLift G I (kernelDerivationEquiv G I hI x))

@[simp]
theorem formalPoint_coordinates (hI : I ^ 2 = ⊥) (x : kernel G I) :
    pointCoordinates G (formalPoint G I hI x) =
      idealDerivationLift G I (kernelDerivationEquiv G I hI x) :=
  (pointCoordinates G).apply_symm_apply _

/-- The formal point reduces to the actual group identity. -/
theorem formalPoint_fst (hI : I ^ 2 = ⊥) (x : kernel G I) :
    affineMap G (TrivSqZeroExt.fstHom R A I) (formalPoint G I hI x) = 1 := by
  apply (pointCoordinates G).injective
  rw [pointCoordinates_naturality, formalPoint_coordinates, pointCoordinates_one]
  rfl

/-- Add the actual ideal component to the constant component. -/
def collapse (hI : I ^ 2 = ⊥) : TrivSqZeroExt A I →ₐ[R] A :=
  TrivSqZeroExt.lift (AlgHom.id R A) (I.restrictScalars R).subtype
    (fun x y => by
      have h : (x : A) * y ∈ I ^ 2 := by
        rw [pow_two]
        exact Ideal.mul_mem_mul x.property y.property
      change (x : A) * (y : A) = 0
      simpa only [hI, Ideal.mem_bot] using h)
    (fun _ _ => rfl)
    (fun r x => by
      change ((MulOpposite.op r • x : I) : A) = (x : A) * r
      rw [op_smul_eq_smul]
      exact mul_comm _ _)

@[simp]
theorem collapse_apply (hI : I ^ 2 = ⊥) (z : TrivSqZeroExt A I) :
    collapse (R := R) I hI z = z.fst + (z.snd : A) := rfl

/-- Collapsing the formal split extension recovers the prescribed actual
kernel point. -/
theorem formalPoint_collapse (hI : I ^ 2 = ⊥) (x : kernel G I) :
    affineMap G (collapse (R := R) I hI) (formalPoint G I hI x) = x.val := by
  apply (pointCoordinates G).injective
  rw [pointCoordinates_naturality, formalPoint_coordinates]
  ext b
  change algebraMap (coordinateAlgebra G) A b +
      (kernelDerivationEquiv G I hI x b : A) = pointCoordinates G x.val b
  rw [kernelDerivationEquiv_apply]
  abel

omit [IsAffineHom G.X.hom] in
/-- A zero map on the formal ideal sends a point reducing to one to one. -/
theorem squarePointMap_zero_of_fst_eq_one
    {x : AffinePoints G (TrivSqZeroExt A I)}
    (hx : affineMap G (TrivSqZeroExt.fstHom R A I) x = 1) :
    squarePointMap G (0 : I →ₗ[A] I) x = 1 := by
  rw [squarePointMap, squareMap_zero, affineMap_comp, hx, map_one]

/-- The infinitesimal coordinate of the product of two formal kernel points
is the sum of their infinitesimal coordinates. -/
theorem formalKernel_coordinate_mul
    (x y : AffinePoints G (TrivSqZeroExt A I))
    (hx : affineMap G (TrivSqZeroExt.fstHom R A I) x = 1)
    (hy : affineMap G (TrivSqZeroExt.fstHom R A I) y = 1)
    (b : coordinateAlgebra G) :
    (pointCoordinates G (x * y) b).snd =
      (pointCoordinates G x b).snd + (pointCoordinates G y b).snd := by
  let z : AffinePoints G (TrivSqZeroExt A (I × I)) :=
    squarePointMap G (LinearMap.inl A I I) x *
      squarePointMap G (LinearMap.inr A I I) y
  have hz₁ : squarePointMap G (LinearMap.fst A I I) z = x := by
    dsimp only [z]
    rw [map_mul, ← squarePointMap_comp, ← squarePointMap_comp,
      LinearMap.fst_comp_inl, LinearMap.fst_comp_inr, squarePointMap_id,
      squarePointMap_zero_of_fst_eq_one G I hy, mul_one]
  have hz₂ : squarePointMap G (LinearMap.snd A I I) z = y := by
    dsimp only [z]
    rw [map_mul, ← squarePointMap_comp, ← squarePointMap_comp,
      LinearMap.snd_comp_inl, LinearMap.snd_comp_inr, squarePointMap_id,
      squarePointMap_zero_of_fst_eq_one G I hx, one_mul]
  have hsum : squarePointMap G
      (LinearMap.id.coprod LinearMap.id : I × I →ₗ[A] I) z = x * y := by
    dsimp only [z]
    rw [map_mul, ← squarePointMap_comp, ← squarePointMap_comp,
      LinearMap.coprod_inl, LinearMap.coprod_inr,
      squarePointMap_id, squarePointMap_id]
  have h₁ := congrArg (fun p => (pointCoordinates G p b).snd) hz₁
  have h₂ := congrArg (fun p => (pointCoordinates G p b).snd) hz₂
  have hs := congrArg (fun p => (pointCoordinates G p b).snd) hsum
  simp only [squarePointMap, pointCoordinates_naturality, AlgHom.comp_apply,
    squareMap_snd, LinearMap.fst_apply] at h₁
  simp only [squarePointMap, pointCoordinates_naturality, AlgHom.comp_apply,
    squareMap_snd, LinearMap.snd_apply] at h₂
  simp only [squarePointMap, pointCoordinates_naturality, AlgHom.comp_apply,
    squareMap_snd, LinearMap.coprod_apply, LinearMap.id_apply] at hs
  exact hs.symm.trans (congrArg₂ (· + ·) h₁ h₂)

/-- The actual square-zero reduction-kernel product is addition of the
associated ideal-valued coordinate derivations. -/
theorem kernelDerivationEquiv_mul (hI : I ^ 2 = ⊥) (x y : kernel G I) :
    kernelDerivationEquiv G I hI (x * y) =
      kernelDerivationEquiv G I hI x + kernelDerivationEquiv G I hI y := by
  let xhat := formalPoint G I hI x
  let yhat := formalPoint G I hI y
  have hmul : affineMap G (collapse (R := R) I hI) (xhat * yhat) = x.val * y.val := by
    rw [map_mul, formalPoint_collapse, formalPoint_collapse]
  have hfst : affineMap G (TrivSqZeroExt.fstHom R A I) (xhat * yhat) = 1 := by
    rw [map_mul, formalPoint_fst, formalPoint_fst, mul_one]
  ext b
  rw [kernelDerivationEquiv_apply]
  change pointCoordinates G (x.val * y.val) b - algebraMap (coordinateAlgebra G) A b =
    (kernelDerivationEquiv G I hI x b : A) + (kernelDerivationEquiv G I hI y b : A)
  rw [← hmul, pointCoordinates_naturality, AlgHom.comp_apply, collapse_apply]
  have hf := congrArg (fun p => pointCoordinates G p b) hfst
  rw [pointCoordinates_naturality, pointCoordinates_one] at hf
  have hs := formalKernel_coordinate_mul G I xhat yhat
    (formalPoint_fst G I hI x) (formalPoint_fst G I hI y) b
  have hcoord : (pointCoordinates G (xhat * yhat) b).fst =
      algebraMap (coordinateAlgebra G) A b := hf
  rw [hcoord]
  have hs' := congrArg (fun i : I => (i : A)) hs
  rw [hs']
  simp only [xhat, yhat, formalPoint_coordinates]
  change algebraMap (coordinateAlgebra G) A b +
      ((kernelDerivationEquiv G I hI x b : A) +
        (kernelDerivationEquiv G I hI y b : A)) -
      algebraMap (coordinateAlgebra G) A b = _
  abel

/-- The actual square-zero kernel group law is commutative. -/
theorem kernel_mul_comm (hI : I ^ 2 = ⊥) (x y : kernel G I) : x * y = y * x := by
  apply (kernelDerivationEquiv G I hI).injective
  rw [kernelDerivationEquiv_mul, kernelDerivationEquiv_mul, add_comm]

/-- The actual square-zero kernel, written additively, is the additive group
of ideal-valued coordinate derivations. -/
def kernelAddEquiv (hI : I ^ 2 = ⊥) :
    Additive (kernel G I) ≃+ Derivation R (coordinateAlgebra G) I where
  toEquiv := Additive.ofMul.symm.trans (kernelDerivationEquiv G I hI)
  map_add' x y := kernelDerivationEquiv_mul G I hI x.toMul y.toMul

/-- For a smooth affine target the actual square-zero kernel multiplication is
addition in the ideal tensored with the actual Lie module. -/
def kernelTensorAddEquiv [Smooth G.X.hom] (hI : I ^ 2 = ⊥) :
    Additive (kernel G I) ≃+ I ⊗[R] Additive (lieKernel G R) :=
  (kernelAddEquiv G I hI).trans (idealCotangentHomEquiv G I).symm.toAddEquiv |>.trans
    (dualTensorHomEquiv R (identityCotangent G) I).symm.toAddEquiv |>.trans
      (((TensorProduct.congr (kernelIdentityCotangentDualEquiv G).symm
        (LinearEquiv.refl R I)).trans (TensorProduct.comm R _ I)).toAddEquiv)

end Langlands.GroupScheme.Lie.SquareZero
