import Langlands.GroupScheme.Dynamic.UnipotentMonomorphism
import Langlands.GroupScheme.Dynamic.RingPointCoordinates
import Langlands.GroupScheme.Lie.SmoothFiniteProjective

/-! # Actual Lie kernels and cotangents in an explicit corepresentation -/

noncomputable section

universe u

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 400000

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj TensorProduct

namespace Langlands.GroupScheme.Corepresented.LieCoordinates

open Langlands.GroupScheme.Lie

variable {R : CommRingCat.{u}} {F : CommAlgCat.{u} R ⥤ GrpCat.{u}}
  {B : CommAlgCat.{u} R} (e : (F ⋙ forget GrpCat).CorepresentableBy B)

local notation "G" => groupScheme F e

local instance affineGroup : IsAffineHom (G).X.hom := by
  change IsAffineHom (Spec.map _)
  infer_instance

/-- Explicit corepresenting coordinates on affine test points. -/
def pointCoordinates (A : Type u) [CommRing A] [Algebra R A] :
    AffinePoints G A ≃ (B →ₐ[R] A) :=
  RingCoordinates.algHomEquiv F e A

variable {A D : Type u} [CommRing A] [Algebra R A] [CommRing D] [Algebra R D]

theorem pointCoordinates_naturality (f : A →ₐ[R] D) (x : AffinePoints G A) :
    pointCoordinates e D (affineMap G f x) = f.comp (pointCoordinates e A x) :=
  RingCoordinates.algHom_comp f x

theorem pointCoordinates_one :
    pointCoordinates e A (1 : AffinePoints G A) =
      (Algebra.ofId R A).comp (RelativeUnipotent.augmentation e) := by
  apply AlgHom.ext
  intro b
  change pointRing (1 : AffinePoints G A) b =
    algebraMap R A (RelativeUnipotent.augmentation e b)
  rw [pointRing_one]
  change Spec.preimage (Spec.map (CommRingCat.ofHom (algebraMap R A)))
    (counit e b) = _
  rw [Spec.preimage_map]
  rfl

section Derivations

variable [Algebra B A] [IsScalarTower R B A]
  (haug : IsScalarTower.toAlgHom R B A =
    (Algebra.ofId R A).comp (RelativeUnipotent.augmentation e))

/-- Actual identity-kernel points are lifts of the specified augmentation. -/
def kernelCoordinates : lieKernel G A ≃
    {f : B →ₐ[R] DualNumber A //
      (TrivSqZeroExt.fstHom R A A).comp f = IsScalarTower.toAlgHom R B A} where
  toFun x := ⟨pointCoordinates e (DualNumber A) x.val, by
    rw [← pointCoordinates_naturality]
    change pointCoordinates e A (reduction G x.val) = _
    rw [x.property, pointCoordinates_one, haug]⟩
  invFun f := ⟨(pointCoordinates e (DualNumber A)).symm f.val, by
    change reduction G _ = 1
    apply (pointCoordinates e A).injective
    change pointCoordinates e A (affineMap G (TrivSqZeroExt.fstHom R A A) _) = _
    rw [pointCoordinates_naturality, Equiv.apply_symm_apply, f.property,
      pointCoordinates_one, haug]⟩
  left_inv x := Subtype.ext ((pointCoordinates e (DualNumber A)).symm_apply_apply x.val)
  right_inv f := Subtype.ext ((pointCoordinates e (DualNumber A)).apply_symm_apply f.val)

/-- Identity-point derivations in the explicit corepresenting algebra. -/
def kernelDerivationEquiv : lieKernel G A ≃ Derivation R B A :=
  (kernelCoordinates e haug).trans Lie.derivationLiftEquiv.symm

@[simp]
theorem kernelDerivationEquiv_apply (x : lieKernel G A) (b : B) :
    kernelDerivationEquiv e haug x b = (pointCoordinates e (DualNumber A) x.val b).snd := rfl

theorem kernelDerivationEquiv_scale (c : A) (x : lieKernel G A) :
    kernelDerivationEquiv e haug (lieKernelScale G c x) =
      c • kernelDerivationEquiv e haug x := by
  ext b
  change (pointCoordinates e (DualNumber A) (affineMap G
    (GeneralLinear.DualNumber.epsilonScaleAlg (R := R) c) x.val) b).snd =
      c * (pointCoordinates e (DualNumber A) x.val b).snd
  rw [pointCoordinates_naturality]
  exact GeneralLinear.DualNumber.epsilonScale_snd c _

theorem kernelDerivationEquiv_mul (x y : lieKernel G A) :
    kernelDerivationEquiv e haug (x * y) =
      kernelDerivationEquiv e haug x + kernelDerivationEquiv e haug y := by
  let z : AffinePoints G (TrivSqZeroExt A (A × A)) :=
    squarePointMap G (LinearMap.inl A A A) x.val *
      squarePointMap G (LinearMap.inr A A A) y.val
  have hx : squarePointMap G (LinearMap.fst A A A) z = x.val := by
    dsimp only [z]
    simp only [map_mul, ← squarePointMap_comp, LinearMap.fst_comp_inl,
      LinearMap.fst_comp_inr, squarePointMap_id, squarePointMap_zero, mul_one]
  have hy : squarePointMap G (LinearMap.snd A A A) z = y.val := by
    dsimp only [z]
    simp only [map_mul, ← squarePointMap_comp, LinearMap.snd_comp_inl,
      LinearMap.snd_comp_inr, squarePointMap_id, squarePointMap_zero, one_mul]
  have hs : squarePointMap G (LinearMap.id.coprod LinearMap.id : A × A →ₗ[A] A) z =
      x.val * y.val := by
    dsimp only [z]
    simp only [map_mul, ← squarePointMap_comp, LinearMap.coprod_inl,
      LinearMap.coprod_inr, squarePointMap_id]
  ext b
  have hx' := congrArg (fun p => (pointCoordinates e _ p b).snd) hx
  have hy' := congrArg (fun p => (pointCoordinates e _ p b).snd) hy
  have hs' := congrArg (fun p => (pointCoordinates e _ p b).snd) hs
  simp only [squarePointMap, pointCoordinates_naturality, AlgHom.comp_apply,
    squareMap_snd, LinearMap.fst_apply] at hx'
  simp only [squarePointMap, pointCoordinates_naturality, AlgHom.comp_apply,
    squareMap_snd, LinearMap.snd_apply] at hy'
  simp only [squarePointMap, pointCoordinates_naturality, AlgHom.comp_apply,
    squareMap_snd, LinearMap.coprod_apply, LinearMap.id_apply] at hs'
  change (pointCoordinates e (DualNumber A) (x.val * y.val) b).snd =
    (pointCoordinates e (DualNumber A) x.val b).snd +
      (pointCoordinates e (DualNumber A) y.val b).snd
  exact hs'.symm.trans (congrArg₂ (· + ·) hx' hy')

/-- The actual Lie kernel is linearly equivalent to the explicit augmentation derivations. -/
def kernelDerivationLinearEquiv : Additive (lieKernel G A) ≃ₗ[A] Derivation R B A where
  toEquiv := Additive.ofMul.symm.trans (kernelDerivationEquiv e haug)
  map_add' x y := kernelDerivationEquiv_mul e haug x.toMul y.toMul
  map_smul' c x := kernelDerivationEquiv_scale e haug c x.toMul

end Derivations

section Cotangent

variable [Algebra B R] [IsScalarTower R B R]
  (haug : IsScalarTower.toAlgHom R B R = RelativeUnipotent.augmentation e)

/-- The actual Lie kernel is the dual of the cotangent in the explicit presentation. -/
def cotangentDualEquiv :
    Module.Dual R (R ⊗[B] KaehlerDifferential R B) ≃ₗ[R]
      Additive (lieKernel G R) :=
  ((LinearMap.liftBaseChangeEquiv R).symm.trans
    ((KaehlerDifferential.linearMapEquivDerivation R B).restrictScalars R)).trans
      (kernelDerivationLinearEquiv e (by simpa using haug)).symm

/-- A smooth explicit augmentation cotangent is a free line when the actual Lie module is. -/
def cotangentEquivOfLieEquiv [Algebra.Smooth R B]
    (eLie : Additive (lieKernel G R) ≃ₗ[R] R) :
    (R ⊗[B] KaehlerDifferential R B) ≃ₗ[R] R :=
  (Module.evalEquiv R (R ⊗[B] KaehlerDifferential R B)).trans
    (((cotangentDualEquiv e haug).trans eLie).dualMap.symm.trans
      (LinearMap.ringLmapEquivSelf R R R))

end Cotangent

end Langlands.GroupScheme.Corepresented.LieCoordinates
