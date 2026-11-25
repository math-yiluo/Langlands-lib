import Langlands.RingTheory.Coalgebra.TensorConvolution
import Mathlib.LinearAlgebra.Contraction
import Mathlib.RingTheory.HopfAlgebra.Convolution
import Mathlib.RingTheory.HopfAlgebra.TensorProduct
import Mathlib.RingTheory.TensorProduct.Finite

/-! # The convolution dual of a finite projective Hopf algebra -/

noncomputable section

open Module TensorProduct WithConv Coalgebra
open scoped TensorProduct

namespace Langlands.GroupScheme.Cartier.FiniteDual

abbrev Dual (R A : Type*) [CommRing R] [AddCommGroup A] [Module R A] :=
  WithConv (Module.Dual R A)

section Module

variable (R A : Type*) [CommRing R] [AddCommGroup A] [Module R A]
  [Module.Finite R A] [Module.Projective R A]

instance : Module.Finite R (Dual R A) :=
  Module.Finite.of_surjective (WithConv.linearEquiv R _).symm.toLinearMap
    (WithConv.linearEquiv R _).symm.surjective

instance : Module.Projective R (Dual R A) :=
  Module.Projective.of_equiv' (WithConv.linearEquiv R _).symm

/-- The linear equivalence with the double dual is evaluation. -/
def bidualLinear : A ≃ₗ[R] Dual R (Dual R A) :=
  ((Module.evalEquiv R A).trans (WithConv.linearEquiv R (Module.Dual R A)).dualMap).trans
    (WithConv.linearEquiv R _).symm

@[simp] theorem bidualLinear_apply (a : A) (f : Dual R A) : bidualLinear R A a f = f a := rfl

end Module

section TensorPairing

variable {R A B : Type*} [CommRing R] [AddCommGroup A] [AddCommGroup B]
  [Module R A] [Module R B] [Module.Finite R A] [Module.Projective R A]
  [Module.Finite R B] [Module.Projective R B]

/-- The tensor of two duals, viewed as a functional on the tensor of the modules. -/
def tensorDual : Dual R A ⊗[R] Dual R B ≃ₗ[R] Module.Dual R (A ⊗[R] B) :=
  (TensorProduct.congr (WithConv.linearEquiv R _) (WithConv.linearEquiv R _)).trans
    (TensorProduct.dualDistribEquiv R A B)

@[simp] theorem tensorDual_tmul (f : Dual R A) (g : Dual R B) (a : A) (b : B) :
    tensorDual (f ⊗ₜ[R] g) (a ⊗ₜ[R] b) = f a * g b := by
  simp [tensorDual, mul_comm]

theorem tensorDual_ext {p q : Dual R A ⊗[R] Dual R B}
    (h : ∀ a b, tensorDual p (a ⊗ₜ[R] b) = tensorDual q (a ⊗ₜ[R] b)) : p = q :=
  tensorDual.injective (TensorProduct.ext' h)

end TensorPairing

section Coalgebra

variable (R A : Type*) [CommRing R] [CommRing A] [Algebra R A]
  [Module.Finite R A] [Module.Projective R A]

/-- The transpose of multiplication. -/
def dualComul : Dual R A →ₗ[R] Dual R A ⊗[R] Dual R A :=
  tensorDual.symm.toLinearMap.comp
    ((LinearMap.mul' R A).dualMap.comp (WithConv.linearEquiv R _).toLinearMap)

/-- The transpose of the unit. -/
def dualCounit : Dual R A →ₗ[R] R :=
  (Module.Dual.eval R A 1).comp (WithConv.linearEquiv R _).toLinearMap

variable {R A}

@[simp] theorem tensorDual_dualComul (f : Dual R A) (a b : A) :
    tensorDual (dualComul R A f) (a ⊗ₜ[R] b) = f (a * b) := by
  change (tensorDual (tensorDual.symm (f.ofConv.comp (LinearMap.mul' R A)))) _ = _
  rw [LinearEquiv.apply_symm_apply]
  rfl

omit [Module.Finite R A] [Module.Projective R A] in
@[simp] theorem dualCounit_apply (f : Dual R A) : dualCounit R A f = f 1 := rfl

private theorem tensorDual_counit_left (t : Dual R A ⊗[R] Dual R A) (a : A) :
    (TensorProduct.lid R (Dual R A) ((dualCounit R A).rTensor _ t)) a =
      tensorDual t (1 ⊗ₜ[R] a) := by
  induction t using TensorProduct.inductionOn with
  | tmul f g => simp [smul_eq_mul]
  | add t s ht hs => simp [ht, hs]

private theorem tensorDual_counit_right (t : Dual R A ⊗[R] Dual R A) (a : A) :
    (TensorProduct.rid R (Dual R A) ((dualCounit R A).lTensor _ t)) a =
      tensorDual t (a ⊗ₜ[R] 1) := by
  induction t using TensorProduct.inductionOn with
  | tmul f g => simp [smul_eq_mul, mul_comm]
  | add t s ht hs => simp [ht, hs]

private theorem tensorDual_comm (t : Dual R A ⊗[R] Dual R A) (a b : A) :
    tensorDual (TensorProduct.comm R _ _ t) (a ⊗ₜ[R] b) = tensorDual t (b ⊗ₜ[R] a) := by
  induction t using TensorProduct.inductionOn with
  | tmul f g => simp [mul_comm]
  | add t s ht hs => simp [ht, hs]

private def tensorDualThree :
    Dual R A ⊗[R] (Dual R A ⊗[R] Dual R A) ≃ₗ[R]
      Module.Dual R (A ⊗[R] (A ⊗[R] A)) :=
  (TensorProduct.congr (LinearEquiv.refl R _)
    (tensorDual.trans (WithConv.linearEquiv R _).symm)).trans tensorDual

@[simp] private theorem tensorDualThree_tmul (f : Dual R A) (t : Dual R A ⊗[R] Dual R A)
    (a b c : A) : tensorDualThree (f ⊗ₜ[R] t) (a ⊗ₜ[R] (b ⊗ₜ[R] c)) =
      f a * tensorDual t (b ⊗ₜ[R] c) := by
  simp [tensorDualThree]

private theorem tensorDualThree_comul_left (t : Dual R A ⊗[R] Dual R A) (a b c : A) :
    tensorDualThree (TensorProduct.assoc R _ _ _ ((dualComul R A).rTensor _ t))
      (a ⊗ₜ[R] (b ⊗ₜ[R] c)) = tensorDual t ((a * b) ⊗ₜ[R] c) := by
  have key (x : Dual R A ⊗[R] Dual R A) (g : Dual R A) :
      tensorDualThree (TensorProduct.assoc R _ _ _ (x ⊗ₜ[R] g))
        (a ⊗ₜ[R] (b ⊗ₜ[R] c)) = tensorDual x (a ⊗ₜ[R] b) * g c := by
    induction x using TensorProduct.inductionOn with
    | tmul f h => simp [mul_assoc]
    | add x y hx hy => simp only [add_tmul, map_add, LinearMap.add_apply, hx, hy, add_mul]
  induction t using TensorProduct.inductionOn with
  | tmul f g => rw [LinearMap.rTensor_tmul, key, tensorDual_dualComul, tensorDual_tmul]
  | add x y hx hy => simp [hx, hy]

private theorem tensorDualThree_comul_right (t : Dual R A ⊗[R] Dual R A) (a b c : A) :
    tensorDualThree ((dualComul R A).lTensor _ t) (a ⊗ₜ[R] (b ⊗ₜ[R] c)) =
      tensorDual t (a ⊗ₜ[R] (b * c)) := by
  induction t using TensorProduct.inductionOn with
  | tmul f g => simp
  | add x y hx hy => simp [hx, hy]

variable (R A)

/-- The dual of a finite projective commutative algebra is cocommutative. -/
instance dualCoalgebra : Coalgebra R (Dual R A) where
  comul := dualComul R A
  counit := dualCounit R A
  coassoc := by
    apply LinearMap.ext
    intro f
    apply tensorDualThree.injective
    apply TensorProduct.ext'
    intro a z
    induction z using TensorProduct.inductionOn with
    | tmul b c => simp [tensorDualThree_comul_left, tensorDualThree_comul_right, mul_assoc]
    | add x y hx hy => simp only [tmul_add, map_add, hx, hy]
  rTensor_counit_comp_comul := by
    apply LinearMap.ext
    intro f
    apply (TensorProduct.lid R (Dual R A)).injective
    apply WithConv.ext
    apply LinearMap.ext
    intro a
    simp only [LinearMap.comp_apply, TensorProduct.mk_apply, TensorProduct.lid_tmul, one_smul]
    change (TensorProduct.lid R (Dual R A) ((dualCounit R A).rTensor _ (dualComul R A f))) a = f a
    simp [tensorDual_counit_left]
  lTensor_counit_comp_comul := by
    apply LinearMap.ext
    intro f
    apply (TensorProduct.rid R (Dual R A)).injective
    apply WithConv.ext
    apply LinearMap.ext
    intro a
    simp only [LinearMap.comp_apply, LinearMap.flip_apply, TensorProduct.mk_apply,
      TensorProduct.rid_tmul, one_smul]
    change (TensorProduct.rid R (Dual R A) ((dualCounit R A).lTensor _ (dualComul R A f))) a = f a
    simp [tensorDual_counit_right]

instance dualIsCocomm : Coalgebra.IsCocomm R (Dual R A) where
  comm_comp_comul := by
    apply LinearMap.ext
    intro f
    apply tensorDual_ext
    intro a b
    change tensorDual (TensorProduct.comm R _ _ (dualComul R A f)) (a ⊗ₜ[R] b) =
      tensorDual (dualComul R A f) (a ⊗ₜ[R] b)
    simp [tensorDual_comm, mul_comm]

@[simp] theorem tensorDual_comul (f : Dual R A) (a b : A) :
    tensorDual (comul (R := R) f) (a ⊗ₜ[R] b) = f (a * b) :=
  tensorDual_dualComul f a b

@[simp] theorem counit_dual (f : Dual R A) : counit (R := R) f = f 1 := rfl

end Coalgebra

section Bialgebra

variable {R A : Type*} [CommRing R] [CommRing A] [Bialgebra R A] [Coalgebra.IsCocomm R A]
  [Module.Finite R A] [Module.Projective R A]

omit [Coalgebra.IsCocomm R A] in
private theorem tensorDual_mulTensor (f g : Dual R A) :
    tensorDual (f ⊗ₜ[R] g) = (WithConv.mulTensor f g).ofConv :=
  TensorProduct.ext' fun a b => by simp

omit [Coalgebra.IsCocomm R A] in
private theorem tensorDual_mul (s t : Dual R A ⊗[R] Dual R A) :
    tensorDual (s * t) = (toConv (tensorDual s) * toConv (tensorDual t)).ofConv := by
  induction s using TensorProduct.inductionOn with
  | tmul f g =>
    induction t using TensorProduct.inductionOn with
    | tmul h k =>
      simp only [Algebra.TensorProduct.tmul_mul_tmul, tensorDual_mulTensor, toConv_ofConv,
        WithConv.mulTensor_convMul]
    | add t u ht hu =>
      change tensorDual (Algebra.TensorProduct.mul (f ⊗ₜ[R] g) (t + u)) = _
      change tensorDual (Algebra.TensorProduct.mul (f ⊗ₜ[R] g) t) = _ at ht
      change tensorDual (Algebra.TensorProduct.mul (f ⊗ₜ[R] g) u) = _ at hu
      rw [map_add, map_add, ht, hu]
      simp only [map_add, toConv_add, mul_add, ofConv_add]
  | add s u hs hu =>
    change tensorDual (Algebra.TensorProduct.mul (s + u) t) = _
    change tensorDual (Algebra.TensorProduct.mul s t) = _ at hs
    change tensorDual (Algebra.TensorProduct.mul u t) = _ at hu
    rw [map_add, LinearMap.add_apply, map_add, hs, hu]
    simp only [map_add, toConv_add, add_mul, ofConv_add]

omit [Coalgebra.IsCocomm R A] in
private theorem tensorDual_one :
    tensorDual (1 : Dual R A ⊗[R] Dual R A) = counit := by
  apply TensorProduct.ext'
  intro a b
  simp [Algebra.TensorProduct.one_def, mul_comm]

variable (R A) in
/-- Convolution and the transposes of multiplication and unit form a bialgebra. -/
instance dualBialgebra : Bialgebra R (Dual R A) := by
  refine Bialgebra.mk' _ _ ?_ (fun {f g} => ?_) ?_ (fun {f g} => ?_)
  · change (1 : Dual R A) 1 = 1
    simp
  · change (f * g) 1 = f 1 * g 1
    simp [Algebra.TensorProduct.one_def]
  · apply tensorDual_ext
    intro a b
    change tensorDual (dualComul R A 1) (a ⊗ₜ[R] b) = _
    rw [tensorDual_dualComul, tensorDual_one]
    simp [mul_comm]
  · apply tensorDual.injective
    change tensorDual (dualComul R A (f * g)) =
      tensorDual (dualComul R A f * dualComul R A g)
    have transpose (h : Dual R A) :
        tensorDual (dualComul R A h) = h.ofConv.comp (Bialgebra.mulCoalgHom R A).toLinearMap :=
      tensorDual.apply_symm_apply _
    rw [tensorDual_mul, transpose, transpose, transpose]
    exact LinearMap.convMul_comp_coalgHom_distrib f g (Bialgebra.mulCoalgHom R A)

end Bialgebra

section Hopf

variable {R A : Type*} [CommRing R] [CommRing A] [HopfAlgebra R A] [Coalgebra.IsCocomm R A]
  [Module.Finite R A] [Module.Projective R A]

private def dualAntipode : Dual R A →ₗ[R] Dual R A :=
  (WithConv.linearEquiv R _).symm.toLinearMap.comp
    ((HopfAlgebra.antipode R (A := A)).dualMap.comp (WithConv.linearEquiv R _).toLinearMap)

omit [Coalgebra.IsCocomm R A] [Module.Finite R A] [Module.Projective R A] in
@[simp] private theorem dualAntipode_apply (f : Dual R A) (a : A) :
    dualAntipode f a = f (HopfAlgebra.antipode R a) := rfl

omit [Coalgebra.IsCocomm R A] in
private theorem dualAntipode_left (t : Dual R A ⊗[R] Dual R A) (a : A) :
    LinearMap.mul' R (Dual R A) (dualAntipode.rTensor _ t) a =
      tensorDual t ((HopfAlgebra.antipode R).rTensor A (comul a)) := by
  induction t using TensorProduct.inductionOn with
  | tmul f g =>
    have h : LinearMap.mul' R R ∘ₗ TensorProduct.map (dualAntipode f).ofConv g.ofConv =
        (tensorDual (f ⊗ₜ[R] g)).comp ((HopfAlgebra.antipode R).rTensor A) :=
      TensorProduct.ext' fun b c => by simp
    simpa only [LinearMap.rTensor_tmul, LinearMap.mul'_apply, LinearMap.convMul_apply,
      LinearMap.comp_apply, LinearEquiv.coe_coe] using
      LinearMap.congr_fun h (comul (R := R) a)
  | add t s ht hs => simp [ht, hs]

variable (R A) in
/-- The antipode on the convolution dual is the transpose of the original antipode. -/
instance dualHopfAlgebra : HopfAlgebra R (Dual R A) := by
  have h : toConv (dualAntipode (R := R) (A := A)) *
      toConv (LinearMap.id : Dual R A →ₗ[R] Dual R A) = 1 := by
    apply WithConv.ext
    apply LinearMap.ext
    intro f
    apply WithConv.ext
    apply LinearMap.ext
    intro a
    change LinearMap.mul' R (Dual R A) (dualAntipode.rTensor _ (comul f)) a =
      (algebraMap R (Dual R A) (counit f)) a
    rw [dualAntipode_left, LinearMap.convAlgebraMap_apply, counit_dual]
    have ht : tensorDual (comul (R := R) f) = f.ofConv.comp (LinearMap.mul' R A) :=
      TensorProduct.ext' fun b c => by simp
    rw [ht, LinearMap.comp_apply, HopfAlgebra.mul_antipode_rTensor_comul_apply]
    simp [Algebra.algebraMap_eq_smul_one, mul_comm]
  exact HopfAlgebra.ofConvInverse dualAntipode h
    ((mul_comm (toConv (LinearMap.id : Dual R A →ₗ[R] Dual R A)) (toConv dualAntipode)).trans h)

end Hopf

section Bidual

variable (R A : Type*) [CommRing R] [CommRing A] [Bialgebra R A] [Coalgebra.IsCocomm R A]
  [Module.Finite R A] [Module.Projective R A]

private def bidualAlgHom : A →ₐ[R] Dual R (Dual R A) :=
  AlgHom.ofLinearMap (bidualLinear R A).toLinearMap (by
    apply WithConv.ext
    apply LinearMap.ext
    intro f
    change bidualLinear R A 1 f = (1 : Dual R (Dual R A)) f
    simp) (by
    intro a b
    apply WithConv.ext
    apply LinearMap.ext
    intro f
    change bidualLinear R A (a * b) f = (bidualLinear R A a * bidualLinear R A b) f
    have h : LinearMap.mul' R R ∘ₗ
          TensorProduct.map (bidualLinear R A a).ofConv (bidualLinear R A b).ofConv =
        (Module.Dual.eval R _ (a ⊗ₜ[R] b)).comp tensorDual.toLinearMap :=
      TensorProduct.ext' fun g k => by simp
    rw [LinearMap.convMul_apply]
    change _ = (LinearMap.mul' R R ∘ₗ
      TensorProduct.map (bidualLinear R A a).ofConv (bidualLinear R A b).ofConv) (comul f)
    rw [h]
    simp)

omit [Coalgebra.IsCocomm R A] in
private theorem tensorDual_bidualLinear (t : A ⊗[R] A) (f g : Dual R A) :
    tensorDual (TensorProduct.map (bidualLinear R A).toLinearMap (bidualLinear R A).toLinearMap t)
      (f ⊗ₜ[R] g) = tensorDual (f ⊗ₜ[R] g) t := by
  induction t using TensorProduct.inductionOn with
  | tmul a b => simp
  | add t s ht hs => simp [ht, hs]

private def bidualHom : A →ₐc[R] Dual R (Dual R A) := by
  refine BialgHom.ofAlgHom (R := R) (A := A) (B := Dual R (Dual R A)) (bidualAlgHom R A)
    (AlgHom.ext fun a => ?_) (AlgHom.ext fun a => ?_)
  · change counit (R := R) (bidualLinear R A a) = counit a
    simp
  · apply tensorDual_ext
    intro f g
    change tensorDual (TensorProduct.map (bidualLinear R A).toLinearMap
        (bidualLinear R A).toLinearMap (comul a)) (f ⊗ₜ[R] g) =
      tensorDual (comul (R := R) (bidualLinear R A a)) (f ⊗ₜ[R] g)
    rw [tensorDual_bidualLinear, tensorDual_comul, bidualLinear_apply, LinearMap.convMul_apply]
    have h : tensorDual (f ⊗ₜ[R] g) =
        LinearMap.mul' R R ∘ₗ TensorProduct.map f.ofConv g.ofConv :=
      TensorProduct.ext' fun x y => by simp
    exact LinearMap.congr_fun h (comul a)

/-- Evaluation identifies a finite projective bicommutative bialgebra with its double dual. -/
def bidualEquiv : A ≃ₐc[R] Dual R (Dual R A) :=
  BialgEquiv.ofBijective (R := R) (A := A) (B := Dual R (Dual R A)) (bidualHom R A)
    (bidualLinear R A).bijective

@[simp] theorem bidualEquiv_apply (a : A) (f : Dual R A) : bidualEquiv R A a f = f a := rfl

end Bidual

end Langlands.GroupScheme.Cartier.FiniteDual
