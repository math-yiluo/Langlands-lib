/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.AlgebraicGeometry.Fiber
public import Mathlib.RingTheory.Flat.Basic
public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
import WeilConjectures.AlgebraicGeometry.PullbackStalkTensorFlat

/-! # Relative flat scalar extension to a fibre-product stalk

Source: Stacks Project, Algebra, Section Tag 051D, Lemma 10.100.1(1);
Examples, Tag 0FLS, the canonical stalk map.
(blueprint: lem-pc-pullback-stalk-relative-flat-extension).
-/

@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits
open scoped TensorProduct
namespace AlgebraicGeometry
open TensorProduct

namespace RelativeFlatTensorExtension

section
variable {R A B C M N : Type u}
variable [CommRing R] [CommRing A] [CommRing B] [CommRing C]
variable [Algebra R A] [Algebra R B] [Algebra (A ⊗[R] B) C]
variable [AddCommGroup M] [Module R M] [Module A M] [IsScalarTower R A M]
variable [AddCommGroup N] [Module R N] [Module B N] [IsScalarTower R B N]

@[instance_reducible] private noncomputable def tensorRightModule :
    Module B (M ⊗[R] N) :=
  (TensorProduct.comm R M N).toAddEquiv.module B

private lemma tensorRightModule_tmul (b : B) (m : M) (n : N) :
    letI := tensorRightModule (R := R) (B := B) (M := M) (N := N)
    b • (m ⊗ₜ[R] n) = m ⊗ₜ[R] (b • n) := by
  rfl

private lemma tensorRightModule_tower :
    letI := tensorRightModule (R := R) (B := B) (M := M) (N := N)
    IsScalarTower R B (M ⊗[R] N) := by
  exact (TensorProduct.comm R M N).isScalarTower B

private lemma tensorRightModule_comm :
    letI := tensorRightModule (R := R) (B := B) (M := M) (N := N)
    SMulCommClass A B (M ⊗[R] N) := by
  let := tensorRightModule (R := R) (B := B) (M := M) (N := N)
  constructor
  intro a b t
  induction t using TensorProduct.inductionOn with
  | tmul m n => simp only [tensorRightModule_tmul, smul_tmul']
  | add x y hx hy => simp [hx, hy]

@[instance_reducible] private noncomputable def mixedTensorModule :
    Module (A ⊗[R] B) (M ⊗[R] N) := by
  let := tensorRightModule (R := R) (B := B) (M := M) (N := N)
  let := tensorRightModule_tower (R := R) (B := B) (M := M) (N := N)
  let := tensorRightModule_comm (R := R) (A := A) (B := B) (M := M) (N := N)
  exact TensorProduct.Algebra.module

private lemma mixedTensorModule_tmul (a : A) (b : B) (m : M) (n : N) :
    letI := mixedTensorModule (R := R) (A := A) (B := B) (M := M) (N := N)
    (a ⊗ₜ[R] b) • (m ⊗ₜ[R] n) = (a • m) ⊗ₜ[R] (b • n) := by
  rfl


variable [Algebra A C] [Algebra B C]
variable (hA : (algebraMap (A ⊗[R] B) C).comp (algebraMap A (A ⊗[R] B)) =
  algebraMap A C)
variable (hB : (algebraMap (A ⊗[R] B) C).comp
  Algebra.TensorProduct.includeRight.toRingHom = algebraMap B C)

omit [Algebra B C] in
private lemma left_balance (hA : (algebraMap (A ⊗[R] B) C).comp (algebraMap A (A ⊗[R] B)) =
    algebraMap A C) (a : A) (c : C) (m : M) (n : N) :
    letI := mixedTensorModule (R := R) (A := A) (B := B) (M := M) (N := N)
    (a • c) ⊗ₜ[A ⊗[R] B] (m ⊗ₜ[R] n) =
      c ⊗ₜ[A ⊗[R] B] ((a • m) ⊗ₜ[R] n) := by
  let := mixedTensorModule (R := R) (A := A) (B := B) (M := M) (N := N)
  have ha : algebraMap (A ⊗[R] B) C (a ⊗ₜ[R] 1) = algebraMap A C a :=
    DFunLike.congr_fun hA a
  have hq : (a ⊗ₜ[R] (1 : B)) • (m ⊗ₜ[R] n) = (a • m) ⊗ₜ[R] n := by
    simp only [mixedTensorModule_tmul, one_smul]
  rw [← hq, ← TensorProduct.smul_tmul]
  congr 1
  simp only [Algebra.smul_def, ha]

omit [Algebra A C] in
private lemma right_balance (hB : (algebraMap (A ⊗[R] B) C).comp
    Algebra.TensorProduct.includeRight.toRingHom = algebraMap B C) (b : B) (c : C) (m : M) (n : N) :
    letI := mixedTensorModule (R := R) (A := A) (B := B) (M := M) (N := N)
    (b • c) ⊗ₜ[A ⊗[R] B] (m ⊗ₜ[R] n) =
      c ⊗ₜ[A ⊗[R] B] (m ⊗ₜ[R] (b • n)) := by
  let := mixedTensorModule (R := R) (A := A) (B := B) (M := M) (N := N)
  have hb : algebraMap (A ⊗[R] B) C (1 ⊗ₜ[R] b) = algebraMap B C b :=
    DFunLike.congr_fun hB b
  have hq : ((1 : A) ⊗ₜ[R] b) • (m ⊗ₜ[R] n) = m ⊗ₜ[R] (b • n) := by
    simp only [mixedTensorModule_tmul, one_smul]
  rw [← hq, ← TensorProduct.smul_tmul]
  congr 1
  simp only [Algebra.smul_def, hb]

private noncomputable def balancedForwardAux
    (hA : (algebraMap (A ⊗[R] B) C).comp (algebraMap A (A ⊗[R] B)) =
    algebraMap A C) (n : N) :
    letI := mixedTensorModule (R := R) (A := A) (B := B) (M := M) (N := N)
    C ⊗[A] M →+ C ⊗[A ⊗[R] B] (M ⊗[R] N) := by
  let := mixedTensorModule (R := R) (A := A) (B := B) (M := M) (N := N)
  refine TensorProduct.liftAddHom
    { toFun := fun c ↦
        { toFun := fun m ↦ c ⊗ₜ[A ⊗[R] B] (m ⊗ₜ[R] n)
          map_zero' := by simp
          map_add' := by intros; simp [add_tmul, tmul_add] }
      map_zero' := by ext; simp
      map_add' := by intros; ext; simp [add_tmul] } ?_
  intro a c m
  exact left_balance hA a c m n

omit [Algebra B C] in
@[simp] private lemma balancedForwardAux_tmul
    (hA : (algebraMap (A ⊗[R] B) C).comp (algebraMap A (A ⊗[R] B)) =
    algebraMap A C) (c : C) (m : M) (n : N) :
    letI := mixedTensorModule (R := R) (A := A) (B := B) (M := M) (N := N)
    balancedForwardAux hA n (c ⊗ₜ[A] m) = c ⊗ₜ[A ⊗[R] B] (m ⊗ₜ[R] n) := rfl


variable [SMulCommClass A B C]

private noncomputable def balancedForward
    (hA : (algebraMap (A ⊗[R] B) C).comp (algebraMap A (A ⊗[R] B)) =
      algebraMap A C)
    (hB : (algebraMap (A ⊗[R] B) C).comp
      Algebra.TensorProduct.includeRight.toRingHom = algebraMap B C) :
    letI := mixedTensorModule (R := R) (A := A) (B := B) (M := M) (N := N)
    (C ⊗[A] M) ⊗[B] N →+ C ⊗[A ⊗[R] B] (M ⊗[R] N) := by
  let := mixedTensorModule (R := R) (A := A) (B := B) (M := M) (N := N)
  refine TensorProduct.liftAddHom
    { toFun := fun x ↦
        { toFun := fun n ↦ balancedForwardAux hA n x
          map_zero' := by
            induction x using TensorProduct.inductionOn with
            | tmul c m => simp
            | add x y hx hy => simp [hx, hy]
          map_add' := by
            intro n n'
            induction x using TensorProduct.inductionOn with
            | tmul c m => simp [tmul_add]
            | add x y hx hy => simp [hx, hy, add_add_add_comm] }
      map_zero' := by ext; simp
      map_add' := by intros; ext; simp } ?_
  intro b x n
  change balancedForwardAux hA n (b • x) = balancedForwardAux hA (b • n) x
  induction x using TensorProduct.inductionOn with
  | tmul c m =>
    simp only [smul_tmul', balancedForwardAux_tmul]
    exact right_balance hB b c m n
  | add x y hx hy => simp [hx, hy]

@[simp] private lemma balancedForward_tmul
    (hA : (algebraMap (A ⊗[R] B) C).comp (algebraMap A (A ⊗[R] B)) =
      algebraMap A C)
    (hB : (algebraMap (A ⊗[R] B) C).comp
      Algebra.TensorProduct.includeRight.toRingHom = algebraMap B C)
    (c : C) (m : M) (n : N) :
    letI := mixedTensorModule (R := R) (A := A) (B := B) (M := M) (N := N)
    balancedForward hA hB ((c ⊗ₜ[A] m) ⊗ₜ[B] n) =
      c ⊗ₜ[A ⊗[R] B] (m ⊗ₜ[R] n) := rfl


variable [Algebra R C] [IsScalarTower R A C] [IsScalarTower R B C]

private noncomputable def balancedReverseAux (c : C) : M ⊗[R] N →+ (C ⊗[A] M) ⊗[B] N := by
  refine TensorProduct.liftAddHom
    { toFun := fun m ↦
        { toFun := fun n ↦ (c ⊗ₜ[A] m) ⊗ₜ[B] n
          map_zero' := by simp
          map_add' := by intros; simp [tmul_add] }
      map_zero' := by ext; simp
      map_add' := by intros; ext; simp [tmul_add, add_tmul] } ?_
  intro r m n
  change (c ⊗ₜ[A] (r • m)) ⊗ₜ[B] n = (c ⊗ₜ[A] m) ⊗ₜ[B] (r • n)
  rw [← IsScalarTower.algebraMap_smul A, ← TensorProduct.smul_tmul,
    IsScalarTower.algebraMap_smul A,
    ← IsScalarTower.algebraMap_smul B, ← TensorProduct.smul_tmul, smul_tmul',
    IsScalarTower.algebraMap_smul B]

omit [Algebra (A ⊗[R] B) C] in
@[simp] private lemma balancedReverseAux_tmul (c : C) (m : M) (n : N) :
    balancedReverseAux c (m ⊗ₜ[R] n) = (c ⊗ₜ[A] m) ⊗ₜ[B] n := rfl

private noncomputable def balancedReverse
    (hA : (algebraMap (A ⊗[R] B) C).comp (algebraMap A (A ⊗[R] B)) =
      algebraMap A C)
    (hB : (algebraMap (A ⊗[R] B) C).comp
      Algebra.TensorProduct.includeRight.toRingHom = algebraMap B C) :
    letI := mixedTensorModule (R := R) (A := A) (B := B) (M := M) (N := N)
    C ⊗[A ⊗[R] B] (M ⊗[R] N) →+ (C ⊗[A] M) ⊗[B] N := by
  let := mixedTensorModule (R := R) (A := A) (B := B) (M := M) (N := N)
  refine TensorProduct.liftAddHom
    { toFun := balancedReverseAux
      map_zero' := by
        ext x
        induction x using TensorProduct.inductionOn with
        | tmul m n => simp
        | add x y hx hy => simp [hx, hy]
      map_add' := by
        intro c c'
        ext x
        induction x using TensorProduct.inductionOn with
        | tmul m n => simp [add_tmul]
        | add x y hx hy => simp [hx, hy, add_add_add_comm] } ?_
  intro d c q
  change balancedReverseAux (d • c) q = balancedReverseAux c (d • q)
  have hzero : balancedReverseAux (R := R) (A := A) (B := B) (M := M) (N := N) (0 : C) =
      (0 : M ⊗[R] N →+ (C ⊗[A] M) ⊗[B] N) := by
    ext x
    induction x using TensorProduct.inductionOn with
    | tmul m n => simp
    | add x y hx hy => simp [hx, hy]
  have hadd (c c' : C) :
      balancedReverseAux (R := R) (A := A) (B := B) (M := M) (N := N) (c + c') =
      balancedReverseAux c + balancedReverseAux c' := by
    ext x
    induction x using TensorProduct.inductionOn with
    | tmul m n => simp [add_tmul]
    | add x y hx hy => simp [hx, hy, add_add_add_comm]
  induction d using TensorProduct.inductionOn with
  | add d e hd he =>
    rw [add_smul, hadd, AddMonoidHom.add_apply, hd, he, add_smul, map_add]
  | tmul a b =>
    induction q using TensorProduct.inductionOn with
    | add q q' hq hq' => simp [hq, hq']
    | tmul m n =>
      have hd : algebraMap (A ⊗[R] B) C (a ⊗ₜ[R] b) =
          algebraMap A C a * algebraMap B C b := by
        have ht : a ⊗ₜ[R] b = (a ⊗ₜ[R] (1 : B)) * ((1 : A) ⊗ₜ[R] b) := by
          simp
        rw [ht, map_mul]
        have ha : algebraMap (A ⊗[R] B) C (a ⊗ₜ[R] 1) = algebraMap A C a :=
          DFunLike.congr_fun hA a
        have hb : algebraMap (A ⊗[R] B) C (1 ⊗ₜ[R] b) = algebraMap B C b :=
          DFunLike.congr_fun hB b
        rw [ha, hb]
      simp only [mixedTensorModule_tmul, balancedReverseAux_tmul]
      rw [← TensorProduct.smul_tmul (R := B), smul_tmul',
        ← TensorProduct.smul_tmul (R := A)]
      congr 2
      simp only [Algebra.smul_def, hd]
      ring

@[simp] private lemma balancedReverse_tmul
    (hA : (algebraMap (A ⊗[R] B) C).comp (algebraMap A (A ⊗[R] B)) =
      algebraMap A C)
    (hB : (algebraMap (A ⊗[R] B) C).comp
      Algebra.TensorProduct.includeRight.toRingHom = algebraMap B C)
    (c : C) (m : M) (n : N) :
    letI := mixedTensorModule (R := R) (A := A) (B := B) (M := M) (N := N)
    balancedReverse hA hB (c ⊗ₜ[A ⊗[R] B] (m ⊗ₜ[R] n)) =
      (c ⊗ₜ[A] m) ⊗ₜ[B] n := rfl

private noncomputable def balancedEquiv
    (hA : (algebraMap (A ⊗[R] B) C).comp (algebraMap A (A ⊗[R] B)) =
      algebraMap A C)
    (hB : (algebraMap (A ⊗[R] B) C).comp
      Algebra.TensorProduct.includeRight.toRingHom = algebraMap B C) :
    letI := mixedTensorModule (R := R) (A := A) (B := B) (M := M) (N := N)
    (C ⊗[A] M) ⊗[B] N ≃+ C ⊗[A ⊗[R] B] (M ⊗[R] N) := by
  let := mixedTensorModule (R := R) (A := A) (B := B) (M := M) (N := N)
  exact
    { toFun := balancedForward hA hB
      invFun := balancedReverse hA hB
      map_add' := map_add _
      left_inv := fun x ↦ by
        induction x using TensorProduct.inductionOn with
        | add x y hx hy => simp [hx, hy]
        | tmul q n =>
          induction q using TensorProduct.inductionOn with
          | tmul c m => simp
          | add x y hx hy => simp [add_tmul, hx, hy]
      right_inv := fun x ↦ by
        induction x using TensorProduct.inductionOn with
        | add x y hx hy => simp [hx, hy]
        | tmul c q =>
          induction q using TensorProduct.inductionOn with
          | tmul m n => simp
          | add x y hx hy => simp [tmul_add, hx, hy] }

variable {N' : Type u} [AddCommGroup N'] [Module R N'] [Module B N']
  [IsScalarTower R B N']

private noncomputable def mixedTensorMap (f : N →ₗ[B] N') :
    letI := mixedTensorModule (R := R) (A := A) (B := B) (M := M) (N := N)
    letI := mixedTensorModule (R := R) (A := A) (B := B) (M := M) (N := N')
    M ⊗[R] N →ₗ[A ⊗[R] B] M ⊗[R] N' := by
  let := mixedTensorModule (R := R) (A := A) (B := B) (M := M) (N := N)
  let := mixedTensorModule (R := R) (A := A) (B := B) (M := M) (N := N')
  refine
    { toFun := f.restrictScalars R |>.lTensor M
      map_add' := map_add _
      map_smul' := ?_ }
  intro d q
  change (f.restrictScalars R).lTensor M (d • q) =
    d • ((f.restrictScalars R).lTensor M q)
  induction d using TensorProduct.inductionOn with
  | add d d' hd hd' => rw [add_smul, map_add, hd, hd', add_smul]
  | tmul a b =>
    induction q using TensorProduct.inductionOn with
    | add q q' hq hq' => simp [hq, hq']
    | tmul m n => simp only [mixedTensorModule_tmul, LinearMap.lTensor_tmul,
        LinearMap.restrictScalars_apply, map_smul]

omit [Algebra R C] [IsScalarTower R A C] [IsScalarTower R B C] in
private lemma balanced_naturality
    (hA : (algebraMap (A ⊗[R] B) C).comp (algebraMap A (A ⊗[R] B)) =
      algebraMap A C)
    (hB : (algebraMap (A ⊗[R] B) C).comp
      Algebra.TensorProduct.includeRight.toRingHom = algebraMap B C)
    (f : N →ₗ[B] N') (x : (C ⊗[A] M) ⊗[B] N) :
    letI := mixedTensorModule (R := R) (A := A) (B := B) (M := M) (N := N)
    letI := mixedTensorModule (R := R) (A := A) (B := B) (M := M) (N := N')
    balancedForward hA hB (f.lTensor (C ⊗[A] M) x) =
      (mixedTensorMap f).lTensor C (balancedForward hA hB x) := by
  let := mixedTensorModule (R := R) (A := A) (B := B) (M := M) (N := N)
  let := mixedTensorModule (R := R) (A := A) (B := B) (M := M) (N := N')
  induction x using TensorProduct.inductionOn with
  | add x y hx hy => simp [hx, hy]
  | tmul q n =>
    induction q using TensorProduct.inductionOn with
    | add q q' hq hq' =>
      simp only [add_tmul, map_add]
      rw [hq, hq']
    | tmul c m =>
      simp only [LinearMap.lTensor_tmul, balancedForward_tmul]
      rfl


private theorem relative_flat_unbundled
    (hA : (algebraMap (A ⊗[R] B) C).comp (algebraMap A (A ⊗[R] B)) =
      algebraMap A C)
    (hB : (algebraMap (A ⊗[R] B) C).comp
      Algebra.TensorProduct.includeRight.toRingHom = algebraMap B C)
    [Module.Flat R M] [Module.Flat (A ⊗[R] B) C] :
    Module.Flat B (C ⊗[A] M) := by
  rw [Module.Flat.iff_lTensor_preserves_injective_linearMap]
  intro N N' _ _ _ _ f hf
  let : Module R N := Module.compHom N (algebraMap R B)
  let : Module R N' := Module.compHom N' (algebraMap R B)
  let : IsScalarTower R B N := IsScalarTower.of_compHom R B N
  let : IsScalarTower R B N' := IsScalarTower.of_compHom R B N'
  let := mixedTensorModule (R := R) (A := A) (B := B) (M := M) (N := N)
  let := mixedTensorModule (R := R) (A := A) (B := B) (M := M) (N := N')
  have hi : Function.Injective (mixedTensorMap (R := R) (A := A) f (M := M)) :=
    Module.Flat.lTensor_preserves_injective_linearMap (f.restrictScalars R) hf
  have hj := Module.Flat.lTensor_preserves_injective_linearMap (M := C)
    (mixedTensorMap (R := R) (A := A) f (M := M)) hi
  intro x y hxy
  apply (balancedEquiv hA hB (N := N)).injective
  apply hj
  change (mixedTensorMap f).lTensor C (balancedForward hA hB x) =
    (mixedTensorMap f).lTensor C (balancedForward hA hB y)
  rw [← balanced_naturality hA hB f x, ← balanced_naturality hA hB f y, hxy]

end

private theorem relative_tensor_extension
    {R A B C : Type u} [CommRing R] [CommRing A] [CommRing B] [CommRing C]
    [Algebra R A] [Algebra R B] [Algebra (A ⊗[R] B) C]
    (a : A →+* C) (b : B →+* C)
    (hAC : (algebraMap (A ⊗[R] B) C).comp (algebraMap A (A ⊗[R] B)) = a)
    (hBC : (algebraMap (A ⊗[R] B) C).comp
      Algebra.TensorProduct.includeRight.toRingHom = b)
    (M : ModuleCat.{u} A)
    (hM : Module.Flat R ((ModuleCat.restrictScalars (algebraMap R A)).obj M))
    (hC : Module.Flat (A ⊗[R] B) C) :
    Module.Flat B ((ModuleCat.restrictScalars b).obj
      ((ModuleCat.extendScalars a).obj M)) := by
  let : Algebra A C := a.toAlgebra
  let : Algebra B C := b.toAlgebra
  let : Algebra R C := (a.comp (algebraMap R A)).toAlgebra
  let : IsScalarTower R A C := IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
  let : IsScalarTower R B C := IsScalarTower.of_algebraMap_eq fun r ↦ by
    have hr : (algebraMap A (A ⊗[R] B)).comp (algebraMap R A) =
        Algebra.TensorProduct.includeRight.toRingHom.comp (algebraMap R B) := by
      ext r
      simp
    have hc := congrArg (fun k : R →+* A ⊗[R] B ↦
      (algebraMap (A ⊗[R] B) C).comp k) hr
    rw [← RingHom.comp_assoc, hAC, ← RingHom.comp_assoc, hBC] at hc
    exact DFunLike.congr_fun hc r
  let : Module R M := Module.compHom M (algebraMap R A)
  let : IsScalarTower R A M := IsScalarTower.of_compHom R A M
  let : Module.Flat R M := hM
  let : Module.Flat (A ⊗[R] B) C := hC
  let : SMulCommClass A B C := SMulCommClass.of_commMonoid A B C
  exact relative_flat_unbundled (M := M) hAC hBC

end RelativeFlatTensorExtension


/-- Extending a relatively flat module to a fibre-product stalk gives a module flat
 over the new base stalk. This is a statement about an arbitrary module over one
source stalk, independent of any sheaf or global flatness condition.
Source: Stacks Project, Algebra, Tag 051D, Lemma 10.100.1(1), and Examples, Tag 0FLS.
(blueprint: lem-pc-pullback-stalk-relative-flat-extension).

Proof: Write x = fst(z), t = snd(z), s = f(x), and R, A, B, C for the stalk
rings at s, x, t, z. The equality f(x) = p(t), obtained from pullback.condition,
identifies the two base stalks. Give A and B their R-actions via the stalk maps.
Choose affine neighbourhoods of x and t above an affine neighbourhood of s.
The affine fibre product has coordinate ring A0 tensor_R0 B0, and C is its
localization at z. Inverting the elements outside the primes of x and t first
gives A tensor_R B. These elements are already units in C, so C is a further
localization of D = A tensor_R B; its inclusions of A and B are the two projection
stalk maps. The flatness of C over D is the existing fibre-product stalk lemma 0FLS.
For an injection N -> N' of B-modules, R-flatness of M makes M tensor_R N ->
M tensor_R N' injective. Give these tensors their D-actions, with A acting on M
and B on N. D-flatness of C makes the map obtained by C tensor_D (-) injective.
The balanced isomorphism
(C tensor_A M) tensor_B N = C tensor_D (M tensor_R N)
sends (c tensor m) tensor n to c tensor (m tensor n); its inverse has the reverse
formula. The balancing identities follow from the maps A -> C and B -> C and
their agreement on R. These isomorphisms commute with N -> N' on pure tensors.
Thus tensoring the injection with C tensor_A M is injective. The injectivity
criterion for flatness proves B-flatness of C tensor_A M. This proves the conclusion
with the B-action restricted along snd.stalkMap. No flatness of either scheme
morphism and no finite-generation condition on M is needed. For M = 0 all tensors
are zero. Empty fibre products supply no point z. -/
theorem pullback_stalk_relative_flat_extension
    {X S T : Scheme.{u}} (f : X ⟶ S) (p : T ⟶ S) (z : ↥(pullback f p))
    (M : ModuleCat.{u} (X.presheaf.stalk ((pullback.fst f p) z)))
    (hM : Module.Flat (S.presheaf.stalk (f ((pullback.fst f p) z)))
      ((ModuleCat.restrictScalars (f.stalkMap ((pullback.fst f p) z)).hom).obj M)) :
    Module.Flat (T.presheaf.stalk ((pullback.snd f p) z))
      ((ModuleCat.restrictScalars ((pullback.snd f p).stalkMap z).hom).obj
        ((ModuleCat.extendScalars ((pullback.fst f p).stalkMap z).hom).obj M)) := by
  let R := S.presheaf.stalk (f ((pullback.fst f p) z))
  let A := X.presheaf.stalk ((pullback.fst f p) z)
  let B := T.presheaf.stalk ((pullback.snd f p) z)
  let C := (pullback f p).presheaf.stalk z
  let a : A →+* C := ((pullback.fst f p).stalkMap z).hom
  let b : B →+* C := ((pullback.snd f p).stalkMap z).hom
  let ra : R →+* A := (f.stalkMap ((pullback.fst f p) z)).hom
  let e := S.presheaf.stalkCongr (Inseparable.of_eq
    (congrArg (fun φ : pullback f p ⟶ S ↦ φ z) pullback.condition))
  let rb : R →+* B := (p.stalkMap ((pullback.snd f p) z)).hom.comp e.hom.hom
  have hab : a.comp ra = b.comp rb := by
    have h := Scheme.Hom.stalkMap_congr_hom
      ((pullback.fst f p) ≫ f) ((pullback.snd f p) ≫ p) pullback.condition z
    rw [Scheme.Hom.stalkMap_comp, Scheme.Hom.stalkMap_comp] at h
    exact congrArg CommRingCat.Hom.hom h
  let : Algebra R A := ra.toAlgebra
  let : Algebra R B := rb.toAlgebra
  let : Algebra R C := (a.comp ra).toAlgebra
  let aa : A →ₐ[R] C := { a with commutes' := fun r ↦ rfl }
  let bb : B →ₐ[R] C :=
    { b with commutes' := fun r ↦ (DFunLike.congr_fun hab r).symm }
  let d : (A ⊗[R] B) →ₐ[R] C :=
    Algebra.TensorProduct.lift aa bb (fun _ _ ↦ Commute.all _ _)
  let : Algebra (A ⊗[R] B) C := d.toRingHom.toAlgebra
  have hAC : (algebraMap (A ⊗[R] B) C).comp (algebraMap A (A ⊗[R] B)) = a := by
    ext x
    change d (x ⊗ₜ[R] 1) = a x
    simp [d, aa, bb]
  have hBC : (algebraMap (A ⊗[R] B) C).comp
      Algebra.TensorProduct.includeRight.toRingHom = b := by
    ext x
    change d (1 ⊗ₜ[R] x) = b x
    simp [d, aa, bb]
  have hC : Module.Flat (A ⊗[R] B) C :=
    pullback_stalk_tensor_flat p f z rfl rfl hAC hBC
  exact RelativeFlatTensorExtension.relative_tensor_extension a b hAC hBC M hM hC


end AlgebraicGeometry
