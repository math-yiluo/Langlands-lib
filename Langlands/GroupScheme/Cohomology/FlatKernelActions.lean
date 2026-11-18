import Langlands.GroupScheme.Cohomology.AffineModuleActions
import Langlands.GroupScheme.Lie.NonaffineKernelCocycles
import Langlands.GroupScheme.Lie.NonaffineKernelFlat
import Mathlib.AlgebraicGeometry.Morphisms.Flat

/-! # Regular coefficient actions from actual flat square-zero kernels -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry Opposite
open scoped TensorProduct CategoryTheory.MonObj

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000

namespace Langlands.GroupScheme.Cohomology

open Lie.NonaffineKernel Langlands.AlgebraicGeometry.SmoothLifting

variable {R : CommRingCat.{u}} (H : GroupScheme (Spec R))

/-- A flat affine source has a flat chosen coordinate algebra. -/
instance coordinateAlgebra_flat [IsAffineHom H.X.hom] [Flat H.X.hom] :
    Module.Flat R (Lie.coordinateAlgebra H) := by
  apply RingHom.flat_algebraMap_iff.mp
  apply (Flat.SpecMap_iff
    (f := CommRingCat.ofHom (algebraMap R (Lie.coordinateAlgebra H)))).mp
  change Flat ((algSpec R).obj (op (Lie.coordinateAlgebra H))).hom
  rw [← Over.w (Lie.coordinateIso H).hom]
  infer_instance

variable (G : GroupScheme (Spec R)) (I : Ideal R) [Fact (SqZero I)] [Smooth G.X.hom]

/-- Transfer actual linear kernel conjugation to tensor coefficients on a
flat test algebra. -/
def flatConjugationAction (A : CommAlgCat.{u} R) [Module.Flat R A] :
    G.affinePoints A →*
      (ModulePoints (Additive (kernel G I)) A ≃ₗ[A] ModulePoints (Additive (kernel G I)) A) where
  toFun g := (flatKernelEquiv G I A).symm.trans
    ((kernelConjugationAut G (I.map (algebraMap R A)) g).trans (flatKernelEquiv G I A))
  map_one' := by
    apply LinearEquiv.ext
    intro x
    simp only [map_one, LinearEquiv.trans_apply]
    exact (flatKernelEquiv G I A).apply_symm_apply x
  map_mul' g h := by
    apply LinearEquiv.ext
    intro x
    simp only [map_mul, LinearEquiv.trans_apply, LinearEquiv.mul_apply,
      LinearEquiv.symm_apply_apply]

/-- The actual flat-kernel comparison commutes with coefficient extension. -/
theorem flatComparison_naturality {A B : CommAlgCat.{u} R}
    [Module.Flat R A] [Module.Flat R B] (f : A ⟶ B)
    (x : Additive (kernel G (I.map (algebraMap R A)))) :
    modulePointMap (Additive (kernel G I)) f (flatKernelEquiv G I A x) =
      flatKernelEquiv G I B
        (kernelMapAdd G (I.map (algebraMap R A)) f.hom (map_le_map_extended I f.hom) x) := by
  exact (flatKernelEquiv_naturality G I f.hom x).symm

theorem flatComparison_symm_naturality {A B : CommAlgCat.{u} R}
    [Module.Flat R A] [Module.Flat R B] (f : A ⟶ B)
    (x : ModulePoints (Additive (kernel G I)) A) :
    kernelMapAdd G (I.map (algebraMap R A)) f.hom (map_le_map_extended I f.hom)
        ((flatKernelEquiv G I A).symm x) =
      (flatKernelEquiv G I B).symm (modulePointMap (Additive (kernel G I)) f x) := by
  apply (flatKernelEquiv G I B).injective
  rw [← flatComparison_naturality, LinearEquiv.apply_symm_apply,
    LinearEquiv.apply_symm_apply]

/-- Tensor-valued conjugation is natural between flat test algebras. -/
theorem flatConjugationAction_naturality {A B : CommAlgCat.{u} R}
    [Module.Flat R A] [Module.Flat R B] (f : A ⟶ B) (g : G.affinePoints A)
    (x : ModulePoints (Additive (kernel G I)) A) :
    modulePointMap (Additive (kernel G I)) f (flatConjugationAction G I A g x) =
      flatConjugationAction G I B (G.affinePointMap f g)
        (modulePointMap (Additive (kernel G I)) f x) := by
  change modulePointMap (Additive (kernel G I)) f
      (flatKernelEquiv G I A
        (kernelConjugationAut G (I.map (algebraMap R A)) g ((flatKernelEquiv G I A).symm x))) =
    flatKernelEquiv G I B
      (kernelConjugationAut G (I.map (algebraMap R B)) (G.affinePointMap f g)
        ((flatKernelEquiv G I B).symm (modulePointMap (Additive (kernel G I)) f x)))
  rw [flatComparison_naturality, kernelMapAdd_conjugation,
    flatComparison_symm_naturality]
  rfl

variable [IsAffineHom H.X.hom] [Flat H.X.hom]
variable (s : H.X ⟶ G.X)
variable (s₀ : ∀ A : CommAlgCat.{u} R,
  H.affinePoints A →* Lie.AffinePoints G (A ⧸ I.map (algebraMap R A)))
variable (hs : ∀ (A : CommAlgCat.{u} R) (h : H.affinePoints A),
  reduction G (I.map (algebraMap R A)) (h ≫ s) = s₀ A h)

/-- The actual kernel action of a regular lift, transported to tensor
coefficients at a flat test algebra. -/
def liftTensorAction (A : CommAlgCat.{u} R) [Module.Flat R A] :
    H.affinePoints A →*
      (ModulePoints (Additive (kernel G I)) A ≃ₗ[A] ModulePoints (Additive (kernel G I)) A) where
  toFun h := (flatKernelEquiv G I A).symm.trans
    ((reductionLiftAction G (I.map (algebraMap R A))
      (fun h => h ≫ s) (s₀ A) (hs A) h).trans (flatKernelEquiv G I A))
  map_one' := by
    apply LinearEquiv.ext
    intro x
    simp only [map_one, LinearEquiv.trans_apply]
    exact (flatKernelEquiv G I A).apply_symm_apply x
  map_mul' h k := by
    apply LinearEquiv.ext
    intro x
    simp only [map_mul, LinearEquiv.trans_apply, LinearEquiv.mul_apply,
      LinearEquiv.symm_apply_apply]

omit [IsAffineHom H.X.hom] [Flat H.X.hom] in
/-- The transported lift action is natural on flat tests because the original
scheme morphism is regular. -/
theorem liftTensorAction_naturality {A B : CommAlgCat.{u} R}
    [Module.Flat R A] [Module.Flat R B] (f : A ⟶ B) (h : H.affinePoints A)
    (x : ModulePoints (Additive (kernel G I)) A) :
    modulePointMap (Additive (kernel G I)) f (liftTensorAction H G I s s₀ hs A h x) =
      liftTensorAction H G I s s₀ hs B (H.affinePointMap f h)
        (modulePointMap (Additive (kernel G I)) f x) := by
  change modulePointMap (Additive (kernel G I)) f (flatConjugationAction G I A (h ≫ s) x) =
    flatConjugationAction G I B (H.affinePointMap f h ≫ s)
      (modulePointMap (Additive (kernel G I)) f x)
  simpa only [affinePointMap_apply, Category.assoc] using
    flatConjugationAction_naturality G I f (h ≫ s) x

/-- The actual universal conjugation on the flat source coordinates is a
linear coefficient coaction of the base reduction kernel. -/
def liftKernelCoaction :
    Additive (kernel G I) →ₗ[R]
      ModulePoints (Additive (kernel G I)) (Lie.coordinateAlgebra H) :=
  ((liftTensorAction H G I s s₀ hs (Lie.coordinateAlgebra H)
    (genericPoint H)).toLinearMap.restrictScalars R).comp
      (TensorProduct.mk R (Lie.coordinateAlgebra H) (Additive (kernel G I)) 1)

/-- Specializing the universal coaction recovers the actual tensor-valued
kernel action on every flat test algebra. -/
theorem liftKernelCoaction_action (A : CommAlgCat.{u} R) [Module.Flat R A]
    (h : H.affinePoints A) :
    universalCoefficientAction (Additive (kernel G I)) H
        (liftKernelCoaction H G I s s₀ hs) A h =
      (liftTensorAction H G I s s₀ hs A h).toLinearMap := by
  apply LinearMap.ext
  intro x
  induction x using TensorProduct.inductionOn with
  | tmul a m =>
    rw [universalCoefficientAction_tmul]
    change a • modulePointMap (Additive (kernel G I)) (pointSpecialization H h)
      (liftTensorAction H G I s s₀ hs (Lie.coordinateAlgebra H) (genericPoint H)
        ((1 : Lie.coordinateAlgebra H) ⊗ₜ[R] m)) =
      liftTensorAction H G I s s₀ hs A h (a ⊗ₜ[R] m)
    rw [liftTensorAction_naturality, genericPoint_specialize, modulePointMap_tmul, map_one]
    rw [← map_smul]
    simp only [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
  | add x y hx hy => simp only [map_add, hx, hy]

/-- Actual conjugation satisfies the universal identity and multiplication
tests, and therefore defines a regular action on all affine tests. -/
def kernelUniversalModuleAction : UniversalModuleAction (Additive (kernel G I)) H where
  coaction := liftKernelCoaction H G I s s₀ hs
  one m := by
    rw [liftKernelCoaction_action]
    change liftTensorAction H G I s s₀ hs (CommAlgCat.of R R) 1
      ((1 : R) ⊗ₜ[R] m) = _
    rw [map_one]
    rfl
  mul m := by
    let : Module.Flat R (pairCoordinateAlgebra H) := by
      change Module.Flat R (Lie.coordinateAlgebra H ⊗[R] Lie.coordinateAlgebra H)
      infer_instance
    rw [liftKernelCoaction_action, liftKernelCoaction_action, liftKernelCoaction_action]
    change liftTensorAction H G I s s₀ hs (pairCoordinateAlgebra H)
        (genericFirst H * genericSecond H) ((1 : pairCoordinateAlgebra H) ⊗ₜ[R] m) =
      liftTensorAction H G I s s₀ hs (pairCoordinateAlgebra H) (genericFirst H)
        (liftTensorAction H G I s s₀ hs (pairCoordinateAlgebra H) (genericSecond H)
          ((1 : pairCoordinateAlgebra H) ⊗ₜ[R] m))
    rw [map_mul]
    rfl

/-- The base square-zero reduction kernel is an actual regular coefficient
module for the source of a reducing homomorphism, including on nonflat tests. -/
def regularKernelRepresentation : ModuleRepresentation (Additive (kernel G I)) H :=
  (kernelUniversalModuleAction H G I s s₀ hs).moduleRepresentation

/-- On flat tests this regular representation agrees with conjugation on
actual reduction kernels through the canonical scalar-extension comparison. -/
theorem regularKernelRepresentation_action (A : CommAlgCat.{u} R) [Module.Flat R A]
    (h : H.affinePoints A) (x : ModulePoints (Additive (kernel G I)) A) :
    (regularKernelRepresentation H G I s s₀ hs).action A h x =
      flatConjugationAction G I A (h ≫ s) x := by
  change universalCoefficientAction (Additive (kernel G I)) H
    (liftKernelCoaction H G I s s₀ hs) A h x = _
  rw [liftKernelCoaction_action]
  rfl

end Langlands.GroupScheme.Cohomology
