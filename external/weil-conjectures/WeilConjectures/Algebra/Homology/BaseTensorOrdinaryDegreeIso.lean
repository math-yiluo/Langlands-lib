/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRingsExact
public import Mathlib.RingTheory.TensorProduct.Basic
import Mathlib.RingTheory.IsTensorProduct

/-!
# Degreewise ordinary base tensor comparison

Source: Stacks Project, Tags 00CX, 05G3 and 08IB.
(blueprint: lem-pc-base-tensor-ordinary-degree-iso).
-/

@[expose] public section

set_option autoImplicit false

universe uR uA uB v

open CategoryTheory
open scoped TensorProduct ChangeOfRings

namespace ModuleCat

/-- Stacks Project, Tags 00CX and 05G3 (tensor universal property and base change),
and Tag 08IB (affine comparison).
(blueprint: lem-pc-base-tensor-ordinary-degree-iso).

Proof: define the forward B-linear map on generators by
b tensor m ↦ (1 tensor b) tensor m. Define the inverse on double pure tensors by
(a tensor b) tensor m ↦ b tensor (a m). R-balancing follows from the R-algebra
structures on A and B, and A-balancing follows from associativity of the A-action
on M. The first composite fixes b tensor m. The second fixes every double pure
tensor since (1 tensor b) tensor (a m) = (a tensor b) tensor m by A-balancing.
Tensor induction proves both composite identities. The resulting equivalence is
B-linear and has the claimed generator formula. No flatness is required.
Mathlib's Algebra.IsPushout.cancelBaseChange supplies this equivalence; its
symm_tmul lemma supplies the formula after identifying the scalar actions of
ModuleCat's ring-hom-based extension and restriction with the algebra actions. -/
theorem exists_baseTensorOrdinaryDegreeIso
    (R : Type uR) (A : Type uA) (B : Type uB)
    [CommRing R] [CommRing A] [CommRing B] [Algebra R A] [Algebra R B]
    (M : ModuleCat.{max uR uA uB v} A) :
    ∃ e :
      (extendScalars.{_, _, max uR uA uB v} (algebraMap R B)).obj
        ((restrictScalars.{max uR uA uB v} (algebraMap R A)).obj M) ≅
      (restrictScalars.{max uR uA uB v}
        Algebra.TensorProduct.includeRight.toRingHom).obj
        ((extendScalars.{_, _, max uR uA uB v}
          (algebraMap A (A ⊗[R] B))).obj M),
      ∀ (b : B) (m : M), e.hom (b ⊗ₜ[R,algebraMap R B] m) =
        Algebra.TensorProduct.includeRight b ⊗ₜ[A,algebraMap A (A ⊗[R] B)] m := by
  let : Module R M := Module.compHom M (algebraMap R A)
  let : IsScalarTower R A M := IsScalarTower.of_compHom R A M
  let := Algebra.TensorProduct.rightAlgebra (R := R) (A := A) (B := B)
  let X := (extendScalars.{_, _, max uR uA uB v} (algebraMap R B)).obj
    ((restrictScalars.{max uR uA uB v} (algebraMap R A)).obj M)
  let Y := (restrictScalars.{max uR uA uB v}
    Algebra.TensorProduct.includeRight.toRingHom).obj
    ((extendScalars.{_, _, max uR uA uB v} (algebraMap A (A ⊗[R] B))).obj M)
  let f : (restrictScalars (algebraMap R B)).obj (of B B) ≃ₗ[R] B :=
    { AddEquiv.refl B with
      map_smul' := by
        intro r b
        change algebraMap R B r * (show B from b) = r • (show B from b)
        exact (Algebra.smul_def r (show B from b)).symm }
  let fT := TensorProduct.congr f (LinearEquiv.refl R M)
  let fB : X ≃ₗ[B] (B ⊗[R] M) :=
    { fT.toAddEquiv with
      map_smul' := by
        intro b x
        change fT (b • x) = b • fT x
        induction x using TensorProduct.inductionOn with
        | add x y hx hy => simp only [smul_add, map_add, hx, hy]
        | tmul b' m => rfl }
  let g : (A ⊗[R] B) ≃ₗ[A]
      (restrictScalars (algebraMap A (A ⊗[R] B))).obj (of (A ⊗[R] B) (A ⊗[R] B)) :=
    { AddEquiv.refl (A ⊗[R] B) with
      map_smul' := fun a x ↦ Algebra.smul_def a x }
  let gT := TensorProduct.congr g (LinearEquiv.refl A M)
  let gB : ((A ⊗[R] B) ⊗[A] M) ≃ₗ[B] Y :=
    { gT.toAddEquiv with
      map_smul' := by
        intro b x
        change gT (b • x) = b • (show Y from gT x)
        induction x using TensorProduct.inductionOn with
        | add x y hx hy => simp only [smul_add, map_add, hx, hy]
        | tmul c m =>
          change (b • c) ⊗ₜ[A,algebraMap A (A ⊗[R] B)] m =
            (Algebra.TensorProduct.includeRight b * c) ⊗ₜ[A,algebraMap A (A ⊗[R] B)] m
          rw [Algebra.smul_def]
          rfl }
  let e := (Algebra.IsPushout.cancelBaseChange R B A (A ⊗[R] B) M).symm
  refine ⟨(fB.trans (e.trans gB)).toModuleIso, ?_⟩
  intro b m
  change gB (e (fB (b ⊗ₜ[R,algebraMap R B] m))) = _
  change gB (e (b ⊗ₜ[R] m)) = _
  rw [Algebra.IsPushout.cancelBaseChange_symm_tmul]
  rfl

end ModuleCat
