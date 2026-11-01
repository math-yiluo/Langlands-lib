import Langlands.Algebra.NonUnitalModuleDualHomTranspose
import Mathlib.Algebra.Module.PUnit

set_option autoImplicit false

noncomputable section

namespace Langlands.Algebra.NonUnitalModuleDualHomTranspose

open MulOpposite NonUnitalModuleDual

universe uA uV uW uV' uW'

/-! Complete unapplied declarations, with independent algebra and carrier universes. -/

example : {A : Type uA} → [NonUnitalRing A] → [Module ℂ A] →
    [IsScalarTower ℂ A A] → [SMulCommClass ℂ A A] →
    {V : Type uV} → [AddCommGroup V] → [NonUnitalModule Aᵐᵒᵖ V] →
    (hA : IsIdempotented A) → (hV : IsNondegenerate Aᵐᵒᵖ V) →
    NonUnitalModule A (Dual hA.op hV) :=
  @rightDualAction

example : {A : Type uA} → [NonUnitalRing A] → [Module ℂ A] →
    [IsScalarTower ℂ A A] → [SMulCommClass ℂ A A] →
    {V : Type uV} → [AddCommGroup V] → [NonUnitalModule Aᵐᵒᵖ V] →
    (hA : IsIdempotented A) → (hV : IsNondegenerate Aᵐᵒᵖ V) →
    letI := rightDualAction hA hV
    IsNondegenerate A (Dual hA.op hV) :=
  @rightDual_isNondegenerate

example : {A : Type uA} → [NonUnitalRing A] → [Module ℂ A] →
    [IsScalarTower ℂ A A] → [SMulCommClass ℂ A A] →
    {V : Type uV} → [AddCommGroup V] → [NonUnitalModule Aᵐᵒᵖ V] →
    (hA : IsIdempotented A) → (hV : IsNondegenerate Aᵐᵒᵖ V) →
    (a : A) → (ell : Dual hA.op hV) →
    letI := rightDualAction hA hV
    (a • ell).val = ell.val.comp (NondegenerateScalars.toLinearEndHom ℂ hA.op hV (op a)) :=
  @rightDualAction_val

example : {A : Type uA} → [NonUnitalRing A] → [Module ℂ A] →
    [IsScalarTower ℂ A A] → [SMulCommClass ℂ A A] →
    {V : Type uV} → [AddCommGroup V] → [NonUnitalModule Aᵐᵒᵖ V] →
    (hA : IsIdempotented A) → (hV : IsNondegenerate Aᵐᵒᵖ V) →
    (a : A) → (ell : Dual hA.op hV) → (v : V) →
    letI := rightDualAction hA hV
    (a • ell).val v = ell.val (op a • v) :=
  @rightDualAction_apply

example : {A : Type uA} → [NonUnitalRing A] → [Module ℂ A] →
    [IsScalarTower ℂ A A] → [SMulCommClass ℂ A A] →
    {V : Type uV} → [AddCommGroup V] → [NonUnitalModule Aᵐᵒᵖ V] →
    (hA : IsIdempotented A) → (hV : IsNondegenerate Aᵐᵒᵖ V) →
    letI := rightDualAction hA hV
    NondegenerateScalars.complexModule hA (rightDual_isNondegenerate hA hV) =
      dualModule hA.op hV :=
  @rightDual_canonicalModule_eq

example : {A : Type uA} → [NonUnitalRing A] → [Module ℂ A] →
    [IsScalarTower ℂ A A] → [SMulCommClass ℂ A A] →
    {V : Type uV} → [AddCommGroup V] → [NonUnitalModule Aᵐᵒᵖ V] →
    (hA : IsIdempotented A) → (hV : IsNondegenerate Aᵐᵒᵖ V) →
    (c : ℂ) → (ell : Dual hA.op hV) →
    letI := rightDualAction hA hV
    letI := NondegenerateScalars.complexModule hA (rightDual_isNondegenerate hA hV)
    (c • ell).val = c • ell.val :=
  @rightDual_canonical_smul_val

example : {A : Type uA} → [NonUnitalRing A] → [Module ℂ A] →
    [IsScalarTower ℂ A A] → [SMulCommClass ℂ A A] →
    {V : Type uV} → [AddCommGroup V] → [NonUnitalModule Aᵐᵒᵖ V] →
    (hA : IsIdempotented A) → (hV : IsNondegenerate Aᵐᵒᵖ V) →
    (c : ℂ) → (ell : Dual hA.op hV) → (v : V) →
    letI := rightDualAction hA hV
    letI := NondegenerateScalars.complexModule hA (rightDual_isNondegenerate hA hV)
    (c • ell).val v = c • ell.val v :=
  @rightDual_canonical_smul_apply

example : {A : Type uA} → [NonUnitalRing A] → [Module ℂ A] →
    [IsScalarTower ℂ A A] → [SMulCommClass ℂ A A] →
    {V : Type uV} → [AddCommGroup V] → [NonUnitalModule Aᵐᵒᵖ V] →
    {W : Type uW} → [AddCommGroup W] → [NonUnitalModule A W] →
    (hA : IsIdempotented A) → (hV : IsNondegenerate Aᵐᵒᵖ V) →
    (hW : IsNondegenerate A W) →
    Type (max uV uW) :=
  @R

example : {A : Type uA} → [NonUnitalRing A] → [Module ℂ A] →
    [IsScalarTower ℂ A A] → [SMulCommClass ℂ A A] →
    {V : Type uV} → [AddCommGroup V] → [NonUnitalModule Aᵐᵒᵖ V] →
    {W : Type uW} → [AddCommGroup W] → [NonUnitalModule A W] →
    (hA : IsIdempotented A) → (hV : IsNondegenerate Aᵐᵒᵖ V) →
    (hW : IsNondegenerate A W) →
    Type (max uV uW) :=
  @L

example : {A : Type uA} → [NonUnitalRing A] → [Module ℂ A] →
    [IsScalarTower ℂ A A] → [SMulCommClass ℂ A A] →
    {V : Type uV} → [AddCommGroup V] → [NonUnitalModule Aᵐᵒᵖ V] →
    {W : Type uW} → [AddCommGroup W] → [NonUnitalModule A W] →
    (hA : IsIdempotented A) → (hV : IsNondegenerate Aᵐᵒᵖ V) →
    (hW : IsNondegenerate A W) →
    Module ℂ (R hA hV hW) :=
  @rModule

example : {A : Type uA} → [NonUnitalRing A] → [Module ℂ A] →
    [IsScalarTower ℂ A A] → [SMulCommClass ℂ A A] →
    {V : Type uV} → [AddCommGroup V] → [NonUnitalModule Aᵐᵒᵖ V] →
    {W : Type uW} → [AddCommGroup W] → [NonUnitalModule A W] →
    (hA : IsIdempotented A) → (hV : IsNondegenerate Aᵐᵒᵖ V) →
    (hW : IsNondegenerate A W) →
    Module ℂ (L hA hV hW) :=
  @lModule

example : {A : Type uA} → [NonUnitalRing A] → [Module ℂ A] →
    [IsScalarTower ℂ A A] → [SMulCommClass ℂ A A] →
    {V : Type uV} → [AddCommGroup V] → [NonUnitalModule Aᵐᵒᵖ V] →
    {W : Type uW} → [AddCommGroup W] → [NonUnitalModule A W] →
    (hA : IsIdempotented A) → (hV : IsNondegenerate Aᵐᵒᵖ V) →
    (hW : IsNondegenerate A W) →
    letI := fullAction hA hW
    letI := fullAction hA.op hV
    letI := rightDualAction hA hV
    rModule hA hV hW =
      NondegenerateModuleHomScalars.complexHomModule hA.op (isNondegenerate hA hW) :=
  @rModule_eq

example : {A : Type uA} → [NonUnitalRing A] → [Module ℂ A] →
    [IsScalarTower ℂ A A] → [SMulCommClass ℂ A A] →
    {V : Type uV} → [AddCommGroup V] → [NonUnitalModule Aᵐᵒᵖ V] →
    {W : Type uW} → [AddCommGroup W] → [NonUnitalModule A W] →
    (hA : IsIdempotented A) → (hV : IsNondegenerate Aᵐᵒᵖ V) →
    (hW : IsNondegenerate A W) →
    letI := fullAction hA hW
    letI := fullAction hA.op hV
    letI := rightDualAction hA hV
    lModule hA hV hW =
      NondegenerateModuleHomScalars.complexHomModule hA (rightDual_isNondegenerate hA hV) :=
  @lModule_eq

example : {A : Type uA} → [NonUnitalRing A] → [Module ℂ A] →
    [IsScalarTower ℂ A A] → [SMulCommClass ℂ A A] →
    {V : Type uV} → [AddCommGroup V] → [NonUnitalModule Aᵐᵒᵖ V] →
    {W : Type uW} → [AddCommGroup W] → [NonUnitalModule A W] →
    (hA : IsIdempotented A) → (hV : IsNondegenerate Aᵐᵒᵖ V) →
    (hW : IsNondegenerate A W) →
    (c : ℂ) → (φ : R hA hV hW) → (v : V) →
    letI := fullAction hA hW
    letI := fullAction hA.op hV
    letI := rightDualAction hA hV
    letI := rModule hA hV hW
    letI := lModule hA hV hW
    letI := NondegenerateScalars.complexModule hA.op (isNondegenerate hA hW)
    (c • φ) v = c • φ v :=
  @rModule_smul_apply

example : {A : Type uA} → [NonUnitalRing A] → [Module ℂ A] →
    [IsScalarTower ℂ A A] → [SMulCommClass ℂ A A] →
    {V : Type uV} → [AddCommGroup V] → [NonUnitalModule Aᵐᵒᵖ V] →
    {W : Type uW} → [AddCommGroup W] → [NonUnitalModule A W] →
    (hA : IsIdempotented A) → (hV : IsNondegenerate Aᵐᵒᵖ V) →
    (hW : IsNondegenerate A W) →
    (c : ℂ) → (ψ : L hA hV hW) → (w : W) →
    letI := fullAction hA hW
    letI := fullAction hA.op hV
    letI := rightDualAction hA hV
    letI := rModule hA hV hW
    letI := lModule hA hV hW
    letI := NondegenerateScalars.complexModule hA (rightDual_isNondegenerate hA hV)
    (c • ψ) w = c • ψ w :=
  @lModule_smul_apply

example : {A : Type uA} → [NonUnitalRing A] → [Module ℂ A] →
    [IsScalarTower ℂ A A] → [SMulCommClass ℂ A A] →
    {V : Type uV} → [AddCommGroup V] → [NonUnitalModule Aᵐᵒᵖ V] →
    {W : Type uW} → [AddCommGroup W] → [NonUnitalModule A W] →
    (hA : IsIdempotented A) → (hV : IsNondegenerate Aᵐᵒᵖ V) →
    (hW : IsNondegenerate A W) →
    (c : ℂ) → (φ : R hA hV hW) → (v : V) →
    letI := rModule hA hV hW
    letI := lModule hA hV hW
    ((c • φ) v).val = c • (φ v).val :=
  @rModule_smul_val

example : {A : Type uA} → [NonUnitalRing A] → [Module ℂ A] →
    [IsScalarTower ℂ A A] → [SMulCommClass ℂ A A] →
    {V : Type uV} → [AddCommGroup V] → [NonUnitalModule Aᵐᵒᵖ V] →
    {W : Type uW} → [AddCommGroup W] → [NonUnitalModule A W] →
    (hA : IsIdempotented A) → (hV : IsNondegenerate Aᵐᵒᵖ V) →
    (hW : IsNondegenerate A W) →
    (c : ℂ) → (ψ : L hA hV hW) → (w : W) →
    letI := rModule hA hV hW
    letI := lModule hA hV hW
    ((c • ψ) w).val = c • (ψ w).val :=
  @lModule_smul_val

example : {A : Type uA} → [NonUnitalRing A] → [Module ℂ A] →
    [IsScalarTower ℂ A A] → [SMulCommClass ℂ A A] →
    {V : Type uV} → [AddCommGroup V] → [NonUnitalModule Aᵐᵒᵖ V] →
    {W : Type uW} → [AddCommGroup W] → [NonUnitalModule A W] →
    (hA : IsIdempotented A) → (hV : IsNondegenerate Aᵐᵒᵖ V) →
    (hW : IsNondegenerate A W) →
    R hA hV hW → W → FullDual hA.op hV :=
  @transposeFull

example : {A : Type uA} → [NonUnitalRing A] → [Module ℂ A] →
    [IsScalarTower ℂ A A] → [SMulCommClass ℂ A A] →
    {V : Type uV} → [AddCommGroup V] → [NonUnitalModule Aᵐᵒᵖ V] →
    {W : Type uW} → [AddCommGroup W] → [NonUnitalModule A W] →
    (hA : IsIdempotented A) → (hV : IsNondegenerate Aᵐᵒᵖ V) →
    (hW : IsNondegenerate A W) →
    (φ : R hA hV hW) → (w : W) →
    ⇑(transposeFull hA hV hW φ w) = fun v => (φ v).val w :=
  @transposeFull_coe

example : {A : Type uA} → [NonUnitalRing A] → [Module ℂ A] →
    [IsScalarTower ℂ A A] → [SMulCommClass ℂ A A] →
    {V : Type uV} → [AddCommGroup V] → [NonUnitalModule Aᵐᵒᵖ V] →
    {W : Type uW} → [AddCommGroup W] → [NonUnitalModule A W] →
    (hA : IsIdempotented A) → (hV : IsNondegenerate Aᵐᵒᵖ V) →
    (hW : IsNondegenerate A W) →
    (φ : R hA hV hW) → (w : W) → (v : V) →
    transposeFull hA hV hW φ w v = (φ v).val w :=
  @transposeFull_apply

example : {A : Type uA} → [NonUnitalRing A] → [Module ℂ A] →
    [IsScalarTower ℂ A A] → [SMulCommClass ℂ A A] →
    {V : Type uV} → [AddCommGroup V] → [NonUnitalModule Aᵐᵒᵖ V] →
    {W : Type uW} → [AddCommGroup W] → [NonUnitalModule A W] →
    (hA : IsIdempotented A) → (hV : IsNondegenerate Aᵐᵒᵖ V) →
    (hW : IsNondegenerate A W) →
    (φ : R hA hV hW) → (w : W) →
    (e : Idempotent A) → (_he : (e : A) • w = w) → (v : V) →
    transposeFull hA hV hW φ w (op (e : A) • v) = transposeFull hA hV hW φ w v :=
  @transposeFull_fixed

example : {A : Type uA} → [NonUnitalRing A] → [Module ℂ A] →
    [IsScalarTower ℂ A A] → [SMulCommClass ℂ A A] →
    {V : Type uV} → [AddCommGroup V] → [NonUnitalModule Aᵐᵒᵖ V] →
    {W : Type uW} → [AddCommGroup W] → [NonUnitalModule A W] →
    (hA : IsIdempotented A) → (hV : IsNondegenerate Aᵐᵒᵖ V) →
    (hW : IsNondegenerate A W) →
    (φ : R hA hV hW) → (w : W) →
    letI := fullAction hA.op hV
    transposeFull hA hV hW φ w ∈ nondegeneratePart hA.op.op (FullDual hA.op hV) :=
  @transposeFull_mem

example : {A : Type uA} → [NonUnitalRing A] → [Module ℂ A] →
    [IsScalarTower ℂ A A] → [SMulCommClass ℂ A A] →
    {V : Type uV} → [AddCommGroup V] → [NonUnitalModule Aᵐᵒᵖ V] →
    {W : Type uW} → [AddCommGroup W] → [NonUnitalModule A W] →
    (hA : IsIdempotented A) → (hV : IsNondegenerate Aᵐᵒᵖ V) →
    (hW : IsNondegenerate A W) →
    R hA hV hW → L hA hV hW :=
  @transpose

example : {A : Type uA} → [NonUnitalRing A] → [Module ℂ A] →
    [IsScalarTower ℂ A A] → [SMulCommClass ℂ A A] →
    {V : Type uV} → [AddCommGroup V] → [NonUnitalModule Aᵐᵒᵖ V] →
    {W : Type uW} → [AddCommGroup W] → [NonUnitalModule A W] →
    (hA : IsIdempotented A) → (hV : IsNondegenerate Aᵐᵒᵖ V) →
    (hW : IsNondegenerate A W) →
    (φ : R hA hV hW) → (w : W) →
    (transpose hA hV hW φ w).val = transposeFull hA hV hW φ w :=
  @transpose_val

example : {A : Type uA} → [NonUnitalRing A] → [Module ℂ A] →
    [IsScalarTower ℂ A A] → [SMulCommClass ℂ A A] →
    {V : Type uV} → [AddCommGroup V] → [NonUnitalModule Aᵐᵒᵖ V] →
    {W : Type uW} → [AddCommGroup W] → [NonUnitalModule A W] →
    (hA : IsIdempotented A) → (hV : IsNondegenerate Aᵐᵒᵖ V) →
    (hW : IsNondegenerate A W) →
    (φ : R hA hV hW) → (w : W) → (v : V) →
    (transpose hA hV hW φ w).val v = (φ v).val w :=
  @transpose_apply

example : {A : Type uA} → [NonUnitalRing A] → [Module ℂ A] →
    [IsScalarTower ℂ A A] → [SMulCommClass ℂ A A] →
    {V : Type uV} → [AddCommGroup V] → [NonUnitalModule Aᵐᵒᵖ V] →
    {W : Type uW} → [AddCommGroup W] → [NonUnitalModule A W] →
    (hA : IsIdempotented A) → (hV : IsNondegenerate Aᵐᵒᵖ V) →
    (hW : IsNondegenerate A W) →
    (φ : R hA hV hW) → (a : A) → (w : W) →
    letI := rightDualAction hA hV
    transpose hA hV hW φ (a • w) = a • transpose hA hV hW φ w :=
  @transpose_map_smul

example : {A : Type uA} → [NonUnitalRing A] → [Module ℂ A] →
    [IsScalarTower ℂ A A] → [SMulCommClass ℂ A A] →
    {V : Type uV} → [AddCommGroup V] → [NonUnitalModule Aᵐᵒᵖ V] →
    {W : Type uW} → [AddCommGroup W] → [NonUnitalModule A W] →
    (hA : IsIdempotented A) → (hV : IsNondegenerate Aᵐᵒᵖ V) →
    (hW : IsNondegenerate A W) →
    letI := rModule hA hV hW
    letI := lModule hA hV hW
    R hA hV hW →ₗ[ℂ] L hA hV hW :=
  @T

example : {A : Type uA} → [NonUnitalRing A] → [Module ℂ A] →
    [IsScalarTower ℂ A A] → [SMulCommClass ℂ A A] →
    {V : Type uV} → [AddCommGroup V] → [NonUnitalModule Aᵐᵒᵖ V] →
    {W : Type uW} → [AddCommGroup W] → [NonUnitalModule A W] →
    (hA : IsIdempotented A) → (hV : IsNondegenerate Aᵐᵒᵖ V) →
    (hW : IsNondegenerate A W) →
    L hA hV hW → V → FullDual hA hW :=
  @reverseFull

example : {A : Type uA} → [NonUnitalRing A] → [Module ℂ A] →
    [IsScalarTower ℂ A A] → [SMulCommClass ℂ A A] →
    {V : Type uV} → [AddCommGroup V] → [NonUnitalModule Aᵐᵒᵖ V] →
    {W : Type uW} → [AddCommGroup W] → [NonUnitalModule A W] →
    (hA : IsIdempotented A) → (hV : IsNondegenerate Aᵐᵒᵖ V) →
    (hW : IsNondegenerate A W) →
    (ψ : L hA hV hW) → (v : V) →
    ⇑(reverseFull hA hV hW ψ v) = fun w => (ψ w).val v :=
  @reverseFull_coe

example : {A : Type uA} → [NonUnitalRing A] → [Module ℂ A] →
    [IsScalarTower ℂ A A] → [SMulCommClass ℂ A A] →
    {V : Type uV} → [AddCommGroup V] → [NonUnitalModule Aᵐᵒᵖ V] →
    {W : Type uW} → [AddCommGroup W] → [NonUnitalModule A W] →
    (hA : IsIdempotented A) → (hV : IsNondegenerate Aᵐᵒᵖ V) →
    (hW : IsNondegenerate A W) →
    (ψ : L hA hV hW) → (v : V) → (w : W) →
    reverseFull hA hV hW ψ v w = (ψ w).val v :=
  @reverseFull_apply

example : {A : Type uA} → [NonUnitalRing A] → [Module ℂ A] →
    [IsScalarTower ℂ A A] → [SMulCommClass ℂ A A] →
    {V : Type uV} → [AddCommGroup V] → [NonUnitalModule Aᵐᵒᵖ V] →
    {W : Type uW} → [AddCommGroup W] → [NonUnitalModule A W] →
    (hA : IsIdempotented A) → (hV : IsNondegenerate Aᵐᵒᵖ V) →
    (hW : IsNondegenerate A W) →
    (ψ : L hA hV hW) → (v : V) →
    (e : Idempotent Aᵐᵒᵖ) → (_he : (e : Aᵐᵒᵖ) • v = v) → (w : W) →
    reverseFull hA hV hW ψ v ((e : Aᵐᵒᵖ).unop • w) = reverseFull hA hV hW ψ v w :=
  @reverseFull_fixed

example : {A : Type uA} → [NonUnitalRing A] → [Module ℂ A] →
    [IsScalarTower ℂ A A] → [SMulCommClass ℂ A A] →
    {V : Type uV} → [AddCommGroup V] → [NonUnitalModule Aᵐᵒᵖ V] →
    {W : Type uW} → [AddCommGroup W] → [NonUnitalModule A W] →
    (hA : IsIdempotented A) → (hV : IsNondegenerate Aᵐᵒᵖ V) →
    (hW : IsNondegenerate A W) →
    (ψ : L hA hV hW) → (v : V) →
    letI := fullAction hA hW
    reverseFull hA hV hW ψ v ∈ nondegeneratePart hA.op (FullDual hA hW) :=
  @reverseFull_mem

example : {A : Type uA} → [NonUnitalRing A] → [Module ℂ A] →
    [IsScalarTower ℂ A A] → [SMulCommClass ℂ A A] →
    {V : Type uV} → [AddCommGroup V] → [NonUnitalModule Aᵐᵒᵖ V] →
    {W : Type uW} → [AddCommGroup W] → [NonUnitalModule A W] →
    (hA : IsIdempotented A) → (hV : IsNondegenerate Aᵐᵒᵖ V) →
    (hW : IsNondegenerate A W) →
    L hA hV hW → R hA hV hW :=
  @reverse

example : {A : Type uA} → [NonUnitalRing A] → [Module ℂ A] →
    [IsScalarTower ℂ A A] → [SMulCommClass ℂ A A] →
    {V : Type uV} → [AddCommGroup V] → [NonUnitalModule Aᵐᵒᵖ V] →
    {W : Type uW} → [AddCommGroup W] → [NonUnitalModule A W] →
    (hA : IsIdempotented A) → (hV : IsNondegenerate Aᵐᵒᵖ V) →
    (hW : IsNondegenerate A W) →
    (ψ : L hA hV hW) → (v : V) →
    (reverse hA hV hW ψ v).val = reverseFull hA hV hW ψ v :=
  @reverse_val

example : {A : Type uA} → [NonUnitalRing A] → [Module ℂ A] →
    [IsScalarTower ℂ A A] → [SMulCommClass ℂ A A] →
    {V : Type uV} → [AddCommGroup V] → [NonUnitalModule Aᵐᵒᵖ V] →
    {W : Type uW} → [AddCommGroup W] → [NonUnitalModule A W] →
    (hA : IsIdempotented A) → (hV : IsNondegenerate Aᵐᵒᵖ V) →
    (hW : IsNondegenerate A W) →
    (ψ : L hA hV hW) → (v : V) → (w : W) →
    (reverse hA hV hW ψ v).val w = (ψ w).val v :=
  @reverse_apply

example : {A : Type uA} → [NonUnitalRing A] → [Module ℂ A] →
    [IsScalarTower ℂ A A] → [SMulCommClass ℂ A A] →
    {V : Type uV} → [AddCommGroup V] → [NonUnitalModule Aᵐᵒᵖ V] →
    {W : Type uW} → [AddCommGroup W] → [NonUnitalModule A W] →
    (hA : IsIdempotented A) → (hV : IsNondegenerate Aᵐᵒᵖ V) →
    (hW : IsNondegenerate A W) →
    (ψ : L hA hV hW) → (a : Aᵐᵒᵖ) → (v : V) →
    letI := fullAction hA hW
    reverse hA hV hW ψ (a • v) = a • reverse hA hV hW ψ v :=
  @reverse_map_smul

example : {A : Type uA} → [NonUnitalRing A] → [Module ℂ A] →
    [IsScalarTower ℂ A A] → [SMulCommClass ℂ A A] →
    {V : Type uV} → [AddCommGroup V] → [NonUnitalModule Aᵐᵒᵖ V] →
    {W : Type uW} → [AddCommGroup W] → [NonUnitalModule A W] →
    (hA : IsIdempotented A) → (hV : IsNondegenerate Aᵐᵒᵖ V) →
    (hW : IsNondegenerate A W) →
    letI := rModule hA hV hW
    letI := lModule hA hV hW
    L hA hV hW →ₗ[ℂ] R hA hV hW :=
  @S

/-! Unequal algebra/carrier universe directions. -/

example : {A : Type 0} → [NonUnitalRing A] → [Module ℂ A] →
    [IsScalarTower ℂ A A] → [SMulCommClass ℂ A A] →
    {V : Type 1} → [AddCommGroup V] → [NonUnitalModule Aᵐᵒᵖ V] →
    {W : Type 2} → [AddCommGroup W] → [NonUnitalModule A W] →
    (hA : IsIdempotented A) → (hV : IsNondegenerate Aᵐᵒᵖ V) →
    (hW : IsNondegenerate A W) →
    letI := rModule hA hV hW
    letI := lModule hA hV hW
    R hA hV hW →ₗ[ℂ] L hA hV hW :=
  @T

example : {A : Type 0} → [NonUnitalRing A] → [Module ℂ A] →
    [IsScalarTower ℂ A A] → [SMulCommClass ℂ A A] →
    {V : Type 1} → [AddCommGroup V] → [NonUnitalModule Aᵐᵒᵖ V] →
    {W : Type 2} → [AddCommGroup W] → [NonUnitalModule A W] →
    (hA : IsIdempotented A) → (hV : IsNondegenerate Aᵐᵒᵖ V) →
    (hW : IsNondegenerate A W) →
    letI := rModule hA hV hW
    letI := lModule hA hV hW
    L hA hV hW →ₗ[ℂ] R hA hV hW :=
  @S

example : {A : Type 2} → [NonUnitalRing A] → [Module ℂ A] →
    [IsScalarTower ℂ A A] → [SMulCommClass ℂ A A] →
    {V : Type 0} → [AddCommGroup V] → [NonUnitalModule Aᵐᵒᵖ V] →
    {W : Type 1} → [AddCommGroup W] → [NonUnitalModule A W] →
    (hA : IsIdempotented A) → (hV : IsNondegenerate Aᵐᵒᵖ V) →
    (hW : IsNondegenerate A W) →
    letI := rModule hA hV hW
    letI := lModule hA hV hW
    R hA hV hW →ₗ[ℂ] L hA hV hW :=
  @T

example : {A : Type 2} → [NonUnitalRing A] → [Module ℂ A] →
    [IsScalarTower ℂ A A] → [SMulCommClass ℂ A A] →
    {V : Type 0} → [AddCommGroup V] → [NonUnitalModule Aᵐᵒᵖ V] →
    {W : Type 1} → [AddCommGroup W] → [NonUnitalModule A W] →
    (hA : IsIdempotented A) → (hV : IsNondegenerate Aᵐᵒᵖ V) →
    (hW : IsNondegenerate A W) →
    letI := rModule hA hV hW
    letI := lModule hA hV hW
    L hA hV hW →ₗ[ℂ] R hA hV hW :=
  @S

/-! Entire additive/linear packaging and its intrinsic laws. -/

example : {A : Type uA} → [NonUnitalRing A] → [Module ℂ A] →
    [IsScalarTower ℂ A A] → [SMulCommClass ℂ A A] →
    {V : Type uV} → [AddCommGroup V] → [NonUnitalModule Aᵐᵒᵖ V] →
    {W : Type uW} → [AddCommGroup W] → [NonUnitalModule A W] →
    (hA : IsIdempotented A) → (hV : IsNondegenerate Aᵐᵒᵖ V) →
    (hW : IsNondegenerate A W) →
    R hA hV hW →+ L hA hV hW :=
  @transposeAdd

example : {A : Type uA} → [NonUnitalRing A] → [Module ℂ A] →
    [IsScalarTower ℂ A A] → [SMulCommClass ℂ A A] →
    {V : Type uV} → [AddCommGroup V] → [NonUnitalModule Aᵐᵒᵖ V] →
    {W : Type uW} → [AddCommGroup W] → [NonUnitalModule A W] →
    (hA : IsIdempotented A) → (hV : IsNondegenerate Aᵐᵒᵖ V) →
    (hW : IsNondegenerate A W) →
    L hA hV hW →+ R hA hV hW :=
  @reverseAdd

example : {A : Type uA} → [NonUnitalRing A] → [Module ℂ A] →
    [IsScalarTower ℂ A A] → [SMulCommClass ℂ A A] →
    {V : Type uV} → [AddCommGroup V] → [NonUnitalModule Aᵐᵒᵖ V] →
    {W : Type uW} → [AddCommGroup W] → [NonUnitalModule A W] →
    (hA : IsIdempotented A) → (hV : IsNondegenerate Aᵐᵒᵖ V) →
    (hW : IsNondegenerate A W) →
    letI := rModule hA hV hW
    letI := lModule hA hV hW
    (T hA hV hW).toAddMonoidHom = transposeAdd hA hV hW :=
  @T_toAddMonoidHom

example : {A : Type uA} → [NonUnitalRing A] → [Module ℂ A] →
    [IsScalarTower ℂ A A] → [SMulCommClass ℂ A A] →
    {V : Type uV} → [AddCommGroup V] → [NonUnitalModule Aᵐᵒᵖ V] →
    {W : Type uW} → [AddCommGroup W] → [NonUnitalModule A W] →
    (hA : IsIdempotented A) → (hV : IsNondegenerate Aᵐᵒᵖ V) →
    (hW : IsNondegenerate A W) →
    letI := rModule hA hV hW
    letI := lModule hA hV hW
    (S hA hV hW).toAddMonoidHom = reverseAdd hA hV hW :=
  @S_toAddMonoidHom

example : {A : Type uA} → [NonUnitalRing A] → [Module ℂ A] →
    [IsScalarTower ℂ A A] → [SMulCommClass ℂ A A] →
    {V : Type uV} → [AddCommGroup V] → [NonUnitalModule Aᵐᵒᵖ V] →
    {W : Type uW} → [AddCommGroup W] → [NonUnitalModule A W] →
    (hA : IsIdempotented A) → (hV : IsNondegenerate Aᵐᵒᵖ V) →
    (hW : IsNondegenerate A W) →
    letI := rModule hA hV hW
    letI := lModule hA hV hW
    ⇑(T hA hV hW) = transpose hA hV hW :=
  @T_coe

example : {A : Type uA} → [NonUnitalRing A] → [Module ℂ A] →
    [IsScalarTower ℂ A A] → [SMulCommClass ℂ A A] →
    {V : Type uV} → [AddCommGroup V] → [NonUnitalModule Aᵐᵒᵖ V] →
    {W : Type uW} → [AddCommGroup W] → [NonUnitalModule A W] →
    (hA : IsIdempotented A) → (hV : IsNondegenerate Aᵐᵒᵖ V) →
    (hW : IsNondegenerate A W) →
    letI := rModule hA hV hW
    letI := lModule hA hV hW
    ⇑(S hA hV hW) = reverse hA hV hW :=
  @S_coe

example : {A : Type uA} → [NonUnitalRing A] → [Module ℂ A] →
    [IsScalarTower ℂ A A] → [SMulCommClass ℂ A A] →
    {V : Type uV} → [AddCommGroup V] → [NonUnitalModule Aᵐᵒᵖ V] →
    {W : Type uW} → [AddCommGroup W] → [NonUnitalModule A W] →
    (hA : IsIdempotented A) → (hV : IsNondegenerate Aᵐᵒᵖ V) →
    (hW : IsNondegenerate A W) →
    ⇑(transposeAdd hA hV hW) = transpose hA hV hW :=
  @transposeAdd_coe

example : {A : Type uA} → [NonUnitalRing A] → [Module ℂ A] →
    [IsScalarTower ℂ A A] → [SMulCommClass ℂ A A] →
    {V : Type uV} → [AddCommGroup V] → [NonUnitalModule Aᵐᵒᵖ V] →
    {W : Type uW} → [AddCommGroup W] → [NonUnitalModule A W] →
    (hA : IsIdempotented A) → (hV : IsNondegenerate Aᵐᵒᵖ V) →
    (hW : IsNondegenerate A W) →
    ⇑(reverseAdd hA hV hW) = reverse hA hV hW :=
  @reverseAdd_coe

example : {A : Type uA} → [NonUnitalRing A] → [Module ℂ A] →
    [IsScalarTower ℂ A A] → [SMulCommClass ℂ A A] →
    {V : Type uV} → [AddCommGroup V] → [NonUnitalModule Aᵐᵒᵖ V] →
    {W : Type uW} → [AddCommGroup W] → [NonUnitalModule A W] →
    (hA : IsIdempotented A) → (hV : IsNondegenerate Aᵐᵒᵖ V) →
    (hW : IsNondegenerate A W) →
    (φ : R hA hV hW) → letI := rModule hA hV hW
    letI := lModule hA hV hW
    T hA hV hW φ = transpose hA hV hW φ :=
  @T_apply_hom

example : {A : Type uA} → [NonUnitalRing A] → [Module ℂ A] →
    [IsScalarTower ℂ A A] → [SMulCommClass ℂ A A] →
    {V : Type uV} → [AddCommGroup V] → [NonUnitalModule Aᵐᵒᵖ V] →
    {W : Type uW} → [AddCommGroup W] → [NonUnitalModule A W] →
    (hA : IsIdempotented A) → (hV : IsNondegenerate Aᵐᵒᵖ V) →
    (hW : IsNondegenerate A W) →
    (ψ : L hA hV hW) → letI := rModule hA hV hW
    letI := lModule hA hV hW
    S hA hV hW ψ = reverse hA hV hW ψ :=
  @S_apply_hom

example : {A : Type uA} → [NonUnitalRing A] → [Module ℂ A] →
    [IsScalarTower ℂ A A] → [SMulCommClass ℂ A A] →
    {V : Type uV} → [AddCommGroup V] → [NonUnitalModule Aᵐᵒᵖ V] →
    {W : Type uW} → [AddCommGroup W] → [NonUnitalModule A W] →
    (hA : IsIdempotented A) → (hV : IsNondegenerate Aᵐᵒᵖ V) →
    (hW : IsNondegenerate A W) →
    (φ : R hA hV hW) → (w : W) → letI := rModule hA hV hW
    letI := lModule hA hV hW
    (T hA hV hW φ w).val = transposeFull hA hV hW φ w :=
  @T_val

example : {A : Type uA} → [NonUnitalRing A] → [Module ℂ A] →
    [IsScalarTower ℂ A A] → [SMulCommClass ℂ A A] →
    {V : Type uV} → [AddCommGroup V] → [NonUnitalModule Aᵐᵒᵖ V] →
    {W : Type uW} → [AddCommGroup W] → [NonUnitalModule A W] →
    (hA : IsIdempotented A) → (hV : IsNondegenerate Aᵐᵒᵖ V) →
    (hW : IsNondegenerate A W) →
    (ψ : L hA hV hW) → (v : V) → letI := rModule hA hV hW
    letI := lModule hA hV hW
    (S hA hV hW ψ v).val = reverseFull hA hV hW ψ v :=
  @S_val

example : {A : Type uA} → [NonUnitalRing A] → [Module ℂ A] →
    [IsScalarTower ℂ A A] → [SMulCommClass ℂ A A] →
    {V : Type uV} → [AddCommGroup V] → [NonUnitalModule Aᵐᵒᵖ V] →
    {W : Type uW} → [AddCommGroup W] → [NonUnitalModule A W] →
    (hA : IsIdempotented A) → (hV : IsNondegenerate Aᵐᵒᵖ V) →
    (hW : IsNondegenerate A W) →
    (φ : R hA hV hW) → (w : W) → (v : V) → letI := rModule hA hV hW
    letI := lModule hA hV hW
    (T hA hV hW φ w).val v = (φ v).val w :=
  @T_apply

example : {A : Type uA} → [NonUnitalRing A] → [Module ℂ A] →
    [IsScalarTower ℂ A A] → [SMulCommClass ℂ A A] →
    {V : Type uV} → [AddCommGroup V] → [NonUnitalModule Aᵐᵒᵖ V] →
    {W : Type uW} → [AddCommGroup W] → [NonUnitalModule A W] →
    (hA : IsIdempotented A) → (hV : IsNondegenerate Aᵐᵒᵖ V) →
    (hW : IsNondegenerate A W) →
    (ψ : L hA hV hW) → (v : V) → (w : W) → letI := rModule hA hV hW
    letI := lModule hA hV hW
    (S hA hV hW ψ v).val w = (ψ w).val v :=
  @S_apply

example : {A : Type uA} → [NonUnitalRing A] → [Module ℂ A] →
    [IsScalarTower ℂ A A] → [SMulCommClass ℂ A A] →
    {V : Type uV} → [AddCommGroup V] → [NonUnitalModule Aᵐᵒᵖ V] →
    {W : Type uW} → [AddCommGroup W] → [NonUnitalModule A W] →
    (hA : IsIdempotented A) → (hV : IsNondegenerate Aᵐᵒᵖ V) →
    (hW : IsNondegenerate A W) →
    (φ φ1 : R hA hV hW) → letI := rModule hA hV hW
    letI := lModule hA hV hW
    T hA hV hW (φ + φ1) = T hA hV hW φ + T hA hV hW φ1 :=
  @T_map_add

example : {A : Type uA} → [NonUnitalRing A] → [Module ℂ A] →
    [IsScalarTower ℂ A A] → [SMulCommClass ℂ A A] →
    {V : Type uV} → [AddCommGroup V] → [NonUnitalModule Aᵐᵒᵖ V] →
    {W : Type uW} → [AddCommGroup W] → [NonUnitalModule A W] →
    (hA : IsIdempotented A) → (hV : IsNondegenerate Aᵐᵒᵖ V) →
    (hW : IsNondegenerate A W) →
    (ψ ψ1 : L hA hV hW) → letI := rModule hA hV hW
    letI := lModule hA hV hW
    S hA hV hW (ψ + ψ1) = S hA hV hW ψ + S hA hV hW ψ1 :=
  @S_map_add

example : {A : Type uA} → [NonUnitalRing A] → [Module ℂ A] →
    [IsScalarTower ℂ A A] → [SMulCommClass ℂ A A] →
    {V : Type uV} → [AddCommGroup V] → [NonUnitalModule Aᵐᵒᵖ V] →
    {W : Type uW} → [AddCommGroup W] → [NonUnitalModule A W] →
    (hA : IsIdempotented A) → (hV : IsNondegenerate Aᵐᵒᵖ V) →
    (hW : IsNondegenerate A W) →
    (c : ℂ) → (φ : R hA hV hW) → letI := rModule hA hV hW
    letI := lModule hA hV hW
    T hA hV hW (c • φ) = c • T hA hV hW φ :=
  @T_map_smul

example : {A : Type uA} → [NonUnitalRing A] → [Module ℂ A] →
    [IsScalarTower ℂ A A] → [SMulCommClass ℂ A A] →
    {V : Type uV} → [AddCommGroup V] → [NonUnitalModule Aᵐᵒᵖ V] →
    {W : Type uW} → [AddCommGroup W] → [NonUnitalModule A W] →
    (hA : IsIdempotented A) → (hV : IsNondegenerate Aᵐᵒᵖ V) →
    (hW : IsNondegenerate A W) →
    (c : ℂ) → (ψ : L hA hV hW) → letI := rModule hA hV hW
    letI := lModule hA hV hW
    S hA hV hW (c • ψ) = c • S hA hV hW ψ :=
  @S_map_smul

/-! Whole-map naturality in four independent carrier universes. -/

example : {A : Type uA} → [NonUnitalRing A] → [Module ℂ A] →
    [IsScalarTower ℂ A A] → [SMulCommClass ℂ A A] →
    {V : Type uV} → [AddCommGroup V] → [NonUnitalModule Aᵐᵒᵖ V] →
    {W : Type uW} → [AddCommGroup W] → [NonUnitalModule A W] →
    {V' : Type uV'} → [AddCommGroup V'] → [NonUnitalModule Aᵐᵒᵖ V'] →
    {W' : Type uW'} → [AddCommGroup W'] → [NonUnitalModule A W'] →
    (hA : IsIdempotented A) → (hV : IsNondegenerate Aᵐᵒᵖ V) →
    (hW : IsNondegenerate A W) → (hV' : IsNondegenerate Aᵐᵒᵖ V') →
    (hW' : IsNondegenerate A W') →
    (f : NonUnitalModuleHom Aᵐᵒᵖ V' V) → (g : NonUnitalModuleHom A W' W) →
    R hA hV hW →+ R hA hV' hW' :=
  @Rfg

example : {A : Type uA} → [NonUnitalRing A] → [Module ℂ A] →
    [IsScalarTower ℂ A A] → [SMulCommClass ℂ A A] →
    {V : Type uV} → [AddCommGroup V] → [NonUnitalModule Aᵐᵒᵖ V] →
    {W : Type uW} → [AddCommGroup W] → [NonUnitalModule A W] →
    {V' : Type uV'} → [AddCommGroup V'] → [NonUnitalModule Aᵐᵒᵖ V'] →
    {W' : Type uW'} → [AddCommGroup W'] → [NonUnitalModule A W'] →
    (hA : IsIdempotented A) → (hV : IsNondegenerate Aᵐᵒᵖ V) →
    (hW : IsNondegenerate A W) → (hV' : IsNondegenerate Aᵐᵒᵖ V') →
    (hW' : IsNondegenerate A W') →
    (f : NonUnitalModuleHom Aᵐᵒᵖ V' V) → (g : NonUnitalModuleHom A W' W) →
    L hA hV hW →+ L hA hV' hW' :=
  @Lfg

example : {A : Type uA} → [NonUnitalRing A] → [Module ℂ A] →
    [IsScalarTower ℂ A A] → [SMulCommClass ℂ A A] →
    {V : Type uV} → [AddCommGroup V] → [NonUnitalModule Aᵐᵒᵖ V] →
    {W : Type uW} → [AddCommGroup W] → [NonUnitalModule A W] →
    {V' : Type uV'} → [AddCommGroup V'] → [NonUnitalModule Aᵐᵒᵖ V'] →
    {W' : Type uW'} → [AddCommGroup W'] → [NonUnitalModule A W'] →
    (hA : IsIdempotented A) → (hV : IsNondegenerate Aᵐᵒᵖ V) →
    (hW : IsNondegenerate A W) → (hV' : IsNondegenerate Aᵐᵒᵖ V') →
    (hW' : IsNondegenerate A W') →
    (f : NonUnitalModuleHom Aᵐᵒᵖ V' V) → (g : NonUnitalModuleHom A W' W) →
    letI := fullAction hA hW
    letI := fullAction hA hW'
    letI := fullAction hA.op hV
    letI := fullAction hA.op hV'
    letI := rightDualAction hA hV
    letI := rightDualAction hA hV'
    ⇑(Rfg hA hV hW hV' hW' f g) = fun φ => (pullback hA hW' hW g).comp (φ.comp f) :=
  @Rfg_coe

example : {A : Type uA} → [NonUnitalRing A] → [Module ℂ A] →
    [IsScalarTower ℂ A A] → [SMulCommClass ℂ A A] →
    {V : Type uV} → [AddCommGroup V] → [NonUnitalModule Aᵐᵒᵖ V] →
    {W : Type uW} → [AddCommGroup W] → [NonUnitalModule A W] →
    {V' : Type uV'} → [AddCommGroup V'] → [NonUnitalModule Aᵐᵒᵖ V'] →
    {W' : Type uW'} → [AddCommGroup W'] → [NonUnitalModule A W'] →
    (hA : IsIdempotented A) → (hV : IsNondegenerate Aᵐᵒᵖ V) →
    (hW : IsNondegenerate A W) → (hV' : IsNondegenerate Aᵐᵒᵖ V') →
    (hW' : IsNondegenerate A W') →
    (f : NonUnitalModuleHom Aᵐᵒᵖ V' V) → (g : NonUnitalModuleHom A W' W) →
    letI := fullAction hA hW
    letI := fullAction hA hW'
    letI := fullAction hA.op hV
    letI := fullAction hA.op hV'
    letI := rightDualAction hA hV
    letI := rightDualAction hA hV'
    ⇑(Lfg hA hV hW hV' hW' f g) = fun ψ => (fromDoubleOppositeMap (pullback hA.op hV' hV f)).comp (ψ.comp g) :=
  @Lfg_coe

example : {A : Type uA} → [NonUnitalRing A] → [Module ℂ A] →
    [IsScalarTower ℂ A A] → [SMulCommClass ℂ A A] →
    {V : Type uV} → [AddCommGroup V] → [NonUnitalModule Aᵐᵒᵖ V] →
    {W : Type uW} → [AddCommGroup W] → [NonUnitalModule A W] →
    {V' : Type uV'} → [AddCommGroup V'] → [NonUnitalModule Aᵐᵒᵖ V'] →
    {W' : Type uW'} → [AddCommGroup W'] → [NonUnitalModule A W'] →
    (hA : IsIdempotented A) → (hV : IsNondegenerate Aᵐᵒᵖ V) →
    (hW : IsNondegenerate A W) → (hV' : IsNondegenerate Aᵐᵒᵖ V') →
    (hW' : IsNondegenerate A W') →
    (f : NonUnitalModuleHom Aᵐᵒᵖ V' V) → (g : NonUnitalModuleHom A W' W) →
    (φ : R hA hV hW) → letI := fullAction hA hW
    letI := fullAction hA hW'
    letI := fullAction hA.op hV
    letI := fullAction hA.op hV'
    letI := rightDualAction hA hV
    letI := rightDualAction hA hV'
    Rfg hA hV hW hV' hW' f g φ = (pullback hA hW' hW g).comp (φ.comp f) :=
  @Rfg_apply

example : {A : Type uA} → [NonUnitalRing A] → [Module ℂ A] →
    [IsScalarTower ℂ A A] → [SMulCommClass ℂ A A] →
    {V : Type uV} → [AddCommGroup V] → [NonUnitalModule Aᵐᵒᵖ V] →
    {W : Type uW} → [AddCommGroup W] → [NonUnitalModule A W] →
    {V' : Type uV'} → [AddCommGroup V'] → [NonUnitalModule Aᵐᵒᵖ V'] →
    {W' : Type uW'} → [AddCommGroup W'] → [NonUnitalModule A W'] →
    (hA : IsIdempotented A) → (hV : IsNondegenerate Aᵐᵒᵖ V) →
    (hW : IsNondegenerate A W) → (hV' : IsNondegenerate Aᵐᵒᵖ V') →
    (hW' : IsNondegenerate A W') →
    (f : NonUnitalModuleHom Aᵐᵒᵖ V' V) → (g : NonUnitalModuleHom A W' W) →
    (ψ : L hA hV hW) → letI := fullAction hA hW
    letI := fullAction hA hW'
    letI := fullAction hA.op hV
    letI := fullAction hA.op hV'
    letI := rightDualAction hA hV
    letI := rightDualAction hA hV'
    Lfg hA hV hW hV' hW' f g ψ = (fromDoubleOppositeMap (pullback hA.op hV' hV f)).comp (ψ.comp g) :=
  @Lfg_apply

example : {A : Type uA} → [NonUnitalRing A] → [Module ℂ A] →
    [IsScalarTower ℂ A A] → [SMulCommClass ℂ A A] →
    {V : Type uV} → [AddCommGroup V] → [NonUnitalModule Aᵐᵒᵖ V] →
    {W : Type uW} → [AddCommGroup W] → [NonUnitalModule A W] →
    {V' : Type uV'} → [AddCommGroup V'] → [NonUnitalModule Aᵐᵒᵖ V'] →
    {W' : Type uW'} → [AddCommGroup W'] → [NonUnitalModule A W'] →
    (hA : IsIdempotented A) → (hV : IsNondegenerate Aᵐᵒᵖ V) →
    (hW : IsNondegenerate A W) → (hV' : IsNondegenerate Aᵐᵒᵖ V') →
    (hW' : IsNondegenerate A W') →
    (f : NonUnitalModuleHom Aᵐᵒᵖ V' V) → (g : NonUnitalModuleHom A W' W) →
    (φ : R hA hV hW) → (v : V') →
    letI := NondegenerateScalars.complexModule hA hW'
    letI := NondegenerateScalars.complexModule hA hW
    (Rfg hA hV hW hV' hW' f g φ v).val =
      (φ (f v)).val.comp (NondegenerateScalars.complexToLinearMap hA hW' hW g) :=
  @Rfg_val

example : {A : Type uA} → [NonUnitalRing A] → [Module ℂ A] →
    [IsScalarTower ℂ A A] → [SMulCommClass ℂ A A] →
    {V : Type uV} → [AddCommGroup V] → [NonUnitalModule Aᵐᵒᵖ V] →
    {W : Type uW} → [AddCommGroup W] → [NonUnitalModule A W] →
    {V' : Type uV'} → [AddCommGroup V'] → [NonUnitalModule Aᵐᵒᵖ V'] →
    {W' : Type uW'} → [AddCommGroup W'] → [NonUnitalModule A W'] →
    (hA : IsIdempotented A) → (hV : IsNondegenerate Aᵐᵒᵖ V) →
    (hW : IsNondegenerate A W) → (hV' : IsNondegenerate Aᵐᵒᵖ V') →
    (hW' : IsNondegenerate A W') →
    (f : NonUnitalModuleHom Aᵐᵒᵖ V' V) → (g : NonUnitalModuleHom A W' W) →
    (ψ : L hA hV hW) → (w : W') →
    letI := NondegenerateScalars.complexModule hA.op hV'
    letI := NondegenerateScalars.complexModule hA.op hV
    (Lfg hA hV hW hV' hW' f g ψ w).val =
      (ψ (g w)).val.comp (NondegenerateScalars.complexToLinearMap hA.op hV' hV f) :=
  @Lfg_val

example : {A : Type uA} → [NonUnitalRing A] → [Module ℂ A] →
    [IsScalarTower ℂ A A] → [SMulCommClass ℂ A A] →
    {V : Type uV} → [AddCommGroup V] → [NonUnitalModule Aᵐᵒᵖ V] →
    {W : Type uW} → [AddCommGroup W] → [NonUnitalModule A W] →
    {V' : Type uV'} → [AddCommGroup V'] → [NonUnitalModule Aᵐᵒᵖ V'] →
    {W' : Type uW'} → [AddCommGroup W'] → [NonUnitalModule A W'] →
    (hA : IsIdempotented A) → (hV : IsNondegenerate Aᵐᵒᵖ V) →
    (hW : IsNondegenerate A W) → (hV' : IsNondegenerate Aᵐᵒᵖ V') →
    (hW' : IsNondegenerate A W') →
    (f : NonUnitalModuleHom Aᵐᵒᵖ V' V) → (g : NonUnitalModuleHom A W' W) →
    (φ : R hA hV hW) → (v : V') → (w : W') →
    (Rfg hA hV hW hV' hW' f g φ v).val w = (φ (f v)).val (g w) :=
  @Rfg_eval

example : {A : Type uA} → [NonUnitalRing A] → [Module ℂ A] →
    [IsScalarTower ℂ A A] → [SMulCommClass ℂ A A] →
    {V : Type uV} → [AddCommGroup V] → [NonUnitalModule Aᵐᵒᵖ V] →
    {W : Type uW} → [AddCommGroup W] → [NonUnitalModule A W] →
    {V' : Type uV'} → [AddCommGroup V'] → [NonUnitalModule Aᵐᵒᵖ V'] →
    {W' : Type uW'} → [AddCommGroup W'] → [NonUnitalModule A W'] →
    (hA : IsIdempotented A) → (hV : IsNondegenerate Aᵐᵒᵖ V) →
    (hW : IsNondegenerate A W) → (hV' : IsNondegenerate Aᵐᵒᵖ V') →
    (hW' : IsNondegenerate A W') →
    (f : NonUnitalModuleHom Aᵐᵒᵖ V' V) → (g : NonUnitalModuleHom A W' W) →
    (ψ : L hA hV hW) → (w : W') → (v : V') →
    (Lfg hA hV hW hV' hW' f g ψ w).val v = (ψ (g w)).val (f v) :=
  @Lfg_eval

example : {A : Type uA} → [NonUnitalRing A] → [Module ℂ A] →
    [IsScalarTower ℂ A A] → [SMulCommClass ℂ A A] →
    {V : Type uV} → [AddCommGroup V] → [NonUnitalModule Aᵐᵒᵖ V] →
    {W : Type uW} → [AddCommGroup W] → [NonUnitalModule A W] →
    {V' : Type uV'} → [AddCommGroup V'] → [NonUnitalModule Aᵐᵒᵖ V'] →
    {W' : Type uW'} → [AddCommGroup W'] → [NonUnitalModule A W'] →
    (hA : IsIdempotented A) → (hV : IsNondegenerate Aᵐᵒᵖ V) →
    (hW : IsNondegenerate A W) → (hV' : IsNondegenerate Aᵐᵒᵖ V') →
    (hW' : IsNondegenerate A W') →
    (f : NonUnitalModuleHom Aᵐᵒᵖ V' V) → (g : NonUnitalModuleHom A W' W) →
    (transposeAdd hA hV' hW').comp (Rfg hA hV hW hV' hW' f g) =
      (Lfg hA hV hW hV' hW' f g).comp (transposeAdd hA hV hW) :=
  @T_natural

example : {A : Type uA} → [NonUnitalRing A] → [Module ℂ A] →
    [IsScalarTower ℂ A A] → [SMulCommClass ℂ A A] →
    {V : Type uV} → [AddCommGroup V] → [NonUnitalModule Aᵐᵒᵖ V] →
    {W : Type uW} → [AddCommGroup W] → [NonUnitalModule A W] →
    {V' : Type uV'} → [AddCommGroup V'] → [NonUnitalModule Aᵐᵒᵖ V'] →
    {W' : Type uW'} → [AddCommGroup W'] → [NonUnitalModule A W'] →
    (hA : IsIdempotented A) → (hV : IsNondegenerate Aᵐᵒᵖ V) →
    (hW : IsNondegenerate A W) → (hV' : IsNondegenerate Aᵐᵒᵖ V') →
    (hW' : IsNondegenerate A W') →
    (f : NonUnitalModuleHom Aᵐᵒᵖ V' V) → (g : NonUnitalModuleHom A W' W) →
    (reverseAdd hA hV' hW').comp (Lfg hA hV hW hV' hW' f g) =
      (Rfg hA hV hW hV' hW' f g).comp (reverseAdd hA hV hW) :=
  @S_natural

/-! Unequal algebra/four-carrier universe directions for both complete squares. -/

example : {A : Type 0} → [NonUnitalRing A] → [Module ℂ A] →
    [IsScalarTower ℂ A A] → [SMulCommClass ℂ A A] →
    {V : Type 1} → [AddCommGroup V] → [NonUnitalModule Aᵐᵒᵖ V] →
    {W : Type 2} → [AddCommGroup W] → [NonUnitalModule A W] →
    {V' : Type 3} → [AddCommGroup V'] → [NonUnitalModule Aᵐᵒᵖ V'] →
    {W' : Type 4} → [AddCommGroup W'] → [NonUnitalModule A W'] →
    (hA : IsIdempotented A) → (hV : IsNondegenerate Aᵐᵒᵖ V) →
    (hW : IsNondegenerate A W) → (hV' : IsNondegenerate Aᵐᵒᵖ V') →
    (hW' : IsNondegenerate A W') →
    (f : NonUnitalModuleHom Aᵐᵒᵖ V' V) → (g : NonUnitalModuleHom A W' W) →
    R hA hV hW →+ R hA hV' hW' :=
  @Rfg

example : {A : Type 0} → [NonUnitalRing A] → [Module ℂ A] →
    [IsScalarTower ℂ A A] → [SMulCommClass ℂ A A] →
    {V : Type 1} → [AddCommGroup V] → [NonUnitalModule Aᵐᵒᵖ V] →
    {W : Type 2} → [AddCommGroup W] → [NonUnitalModule A W] →
    {V' : Type 3} → [AddCommGroup V'] → [NonUnitalModule Aᵐᵒᵖ V'] →
    {W' : Type 4} → [AddCommGroup W'] → [NonUnitalModule A W'] →
    (hA : IsIdempotented A) → (hV : IsNondegenerate Aᵐᵒᵖ V) →
    (hW : IsNondegenerate A W) → (hV' : IsNondegenerate Aᵐᵒᵖ V') →
    (hW' : IsNondegenerate A W') →
    (f : NonUnitalModuleHom Aᵐᵒᵖ V' V) → (g : NonUnitalModuleHom A W' W) →
    L hA hV hW →+ L hA hV' hW' :=
  @Lfg

example : {A : Type 0} → [NonUnitalRing A] → [Module ℂ A] →
    [IsScalarTower ℂ A A] → [SMulCommClass ℂ A A] →
    {V : Type 1} → [AddCommGroup V] → [NonUnitalModule Aᵐᵒᵖ V] →
    {W : Type 2} → [AddCommGroup W] → [NonUnitalModule A W] →
    {V' : Type 3} → [AddCommGroup V'] → [NonUnitalModule Aᵐᵒᵖ V'] →
    {W' : Type 4} → [AddCommGroup W'] → [NonUnitalModule A W'] →
    (hA : IsIdempotented A) → (hV : IsNondegenerate Aᵐᵒᵖ V) →
    (hW : IsNondegenerate A W) → (hV' : IsNondegenerate Aᵐᵒᵖ V') →
    (hW' : IsNondegenerate A W') →
    (f : NonUnitalModuleHom Aᵐᵒᵖ V' V) → (g : NonUnitalModuleHom A W' W) →
    (transposeAdd hA hV' hW').comp (Rfg hA hV hW hV' hW' f g) =
      (Lfg hA hV hW hV' hW' f g).comp (transposeAdd hA hV hW) :=
  @T_natural

example : {A : Type 0} → [NonUnitalRing A] → [Module ℂ A] →
    [IsScalarTower ℂ A A] → [SMulCommClass ℂ A A] →
    {V : Type 1} → [AddCommGroup V] → [NonUnitalModule Aᵐᵒᵖ V] →
    {W : Type 2} → [AddCommGroup W] → [NonUnitalModule A W] →
    {V' : Type 3} → [AddCommGroup V'] → [NonUnitalModule Aᵐᵒᵖ V'] →
    {W' : Type 4} → [AddCommGroup W'] → [NonUnitalModule A W'] →
    (hA : IsIdempotented A) → (hV : IsNondegenerate Aᵐᵒᵖ V) →
    (hW : IsNondegenerate A W) → (hV' : IsNondegenerate Aᵐᵒᵖ V') →
    (hW' : IsNondegenerate A W') →
    (f : NonUnitalModuleHom Aᵐᵒᵖ V' V) → (g : NonUnitalModuleHom A W' W) →
    (reverseAdd hA hV' hW').comp (Lfg hA hV hW hV' hW' f g) =
      (Rfg hA hV hW hV' hW' f g).comp (reverseAdd hA hV hW) :=
  @S_natural

example : {A : Type 4} → [NonUnitalRing A] → [Module ℂ A] →
    [IsScalarTower ℂ A A] → [SMulCommClass ℂ A A] →
    {V : Type 0} → [AddCommGroup V] → [NonUnitalModule Aᵐᵒᵖ V] →
    {W : Type 1} → [AddCommGroup W] → [NonUnitalModule A W] →
    {V' : Type 2} → [AddCommGroup V'] → [NonUnitalModule Aᵐᵒᵖ V'] →
    {W' : Type 3} → [AddCommGroup W'] → [NonUnitalModule A W'] →
    (hA : IsIdempotented A) → (hV : IsNondegenerate Aᵐᵒᵖ V) →
    (hW : IsNondegenerate A W) → (hV' : IsNondegenerate Aᵐᵒᵖ V') →
    (hW' : IsNondegenerate A W') →
    (f : NonUnitalModuleHom Aᵐᵒᵖ V' V) → (g : NonUnitalModuleHom A W' W) →
    R hA hV hW →+ R hA hV' hW' :=
  @Rfg

example : {A : Type 4} → [NonUnitalRing A] → [Module ℂ A] →
    [IsScalarTower ℂ A A] → [SMulCommClass ℂ A A] →
    {V : Type 0} → [AddCommGroup V] → [NonUnitalModule Aᵐᵒᵖ V] →
    {W : Type 1} → [AddCommGroup W] → [NonUnitalModule A W] →
    {V' : Type 2} → [AddCommGroup V'] → [NonUnitalModule Aᵐᵒᵖ V'] →
    {W' : Type 3} → [AddCommGroup W'] → [NonUnitalModule A W'] →
    (hA : IsIdempotented A) → (hV : IsNondegenerate Aᵐᵒᵖ V) →
    (hW : IsNondegenerate A W) → (hV' : IsNondegenerate Aᵐᵒᵖ V') →
    (hW' : IsNondegenerate A W') →
    (f : NonUnitalModuleHom Aᵐᵒᵖ V' V) → (g : NonUnitalModuleHom A W' W) →
    L hA hV hW →+ L hA hV' hW' :=
  @Lfg

example : {A : Type 4} → [NonUnitalRing A] → [Module ℂ A] →
    [IsScalarTower ℂ A A] → [SMulCommClass ℂ A A] →
    {V : Type 0} → [AddCommGroup V] → [NonUnitalModule Aᵐᵒᵖ V] →
    {W : Type 1} → [AddCommGroup W] → [NonUnitalModule A W] →
    {V' : Type 2} → [AddCommGroup V'] → [NonUnitalModule Aᵐᵒᵖ V'] →
    {W' : Type 3} → [AddCommGroup W'] → [NonUnitalModule A W'] →
    (hA : IsIdempotented A) → (hV : IsNondegenerate Aᵐᵒᵖ V) →
    (hW : IsNondegenerate A W) → (hV' : IsNondegenerate Aᵐᵒᵖ V') →
    (hW' : IsNondegenerate A W') →
    (f : NonUnitalModuleHom Aᵐᵒᵖ V' V) → (g : NonUnitalModuleHom A W' W) →
    (transposeAdd hA hV' hW').comp (Rfg hA hV hW hV' hW' f g) =
      (Lfg hA hV hW hV' hW' f g).comp (transposeAdd hA hV hW) :=
  @T_natural

example : {A : Type 4} → [NonUnitalRing A] → [Module ℂ A] →
    [IsScalarTower ℂ A A] → [SMulCommClass ℂ A A] →
    {V : Type 0} → [AddCommGroup V] → [NonUnitalModule Aᵐᵒᵖ V] →
    {W : Type 1} → [AddCommGroup W] → [NonUnitalModule A W] →
    {V' : Type 2} → [AddCommGroup V'] → [NonUnitalModule Aᵐᵒᵖ V'] →
    {W' : Type 3} → [AddCommGroup W'] → [NonUnitalModule A W'] →
    (hA : IsIdempotented A) → (hV : IsNondegenerate Aᵐᵒᵖ V) →
    (hW : IsNondegenerate A W) → (hV' : IsNondegenerate Aᵐᵒᵖ V') →
    (hW' : IsNondegenerate A W') →
    (f : NonUnitalModuleHom Aᵐᵒᵖ V' V) → (g : NonUnitalModuleHom A W' W) →
    (reverseAdd hA hV' hW').comp (Lfg hA hV hW hV' hW' f g) =
      (Rfg hA hV hW hV' hW' f g).comp (reverseAdd hA hV hW) :=
  @S_natural

/-! Explicit selection in the presence of competing original actions and scalars. -/

section CompetingStructures

set_option linter.overlappingInstances false

variable {A : Type uA} [NonUnitalRing A] [Module ℂ A]
  [IsScalarTower ℂ A A] [SMulCommClass ℂ A A]
  {V : Type uV} [AddCommGroup V] [originalVAction : NonUnitalModule Aᵐᵒᵖ V]
  {W : Type uW} [AddCommGroup W] [originalWAction : NonUnitalModule A W]
  (hA : IsIdempotented A) (hV : IsNondegenerate Aᵐᵒᵖ V) (hW : IsNondegenerate A W)
  [competingVAction : NonUnitalModule Aᵐᵒᵖ V] [competingWAction : NonUnitalModule A W]
  [competingVScalars : Module ℂ V] [competingWScalars : Module ℂ W]

example :
    letI := originalVAction
    letI := originalWAction
    letI := NondegenerateScalars.complexModule hA.op hV
    letI := NondegenerateScalars.complexModule hA hW
    letI := rModule hA hV hW
    letI := lModule hA hV hW
    R hA hV hW →ₗ[ℂ] L hA hV hW :=
  @T A _ _ _ _ V _ originalVAction W _ originalWAction hA hV hW

example :
    letI := originalVAction
    letI := originalWAction
    letI := NondegenerateScalars.complexModule hA.op hV
    letI := NondegenerateScalars.complexModule hA hW
    letI := rModule hA hV hW
    letI := lModule hA hV hW
    L hA hV hW →ₗ[ℂ] R hA hV hW :=
  @S A _ _ _ _ V _ originalVAction W _ originalWAction hA hV hW

example :
    letI := originalVAction
    letI := originalWAction
    ∀ (φ : R hA hV hW) (w : W) (v : V),
      (transpose hA hV hW φ w).val v = (φ v).val w :=
  @transpose_apply A _ _ _ _ V _ originalVAction W _ originalWAction hA hV hW

example :
    letI := originalVAction
    letI := originalWAction
    ∀ (ψ : L hA hV hW) (v : V) (w : W),
      (reverse hA hV hW ψ v).val w = (ψ w).val v :=
  @reverse_apply A _ _ _ _ V _ originalVAction W _ originalWAction hA hV hW

end CompetingStructures

section CompetingHomScalars

set_option linter.overlappingInstances false

variable {A : Type uA} [NonUnitalRing A] [Module ℂ A]
  [IsScalarTower ℂ A A] [SMulCommClass ℂ A A]
  {V : Type uV} [AddCommGroup V] [NonUnitalModule Aᵐᵒᵖ V]
  {W : Type uW} [AddCommGroup W] [NonUnitalModule A W]
  (hA : IsIdempotented A) (hV : IsNondegenerate Aᵐᵒᵖ V) (hW : IsNondegenerate A W)
  [competingRScalars : Module ℂ (R hA hV hW)]
  [competingLScalars : Module ℂ (L hA hV hW)]
  [competingVScalars : Module ℂ V] [competingWScalars : Module ℂ W]

example :
    letI := NondegenerateScalars.complexModule hA.op hV
    letI := NondegenerateScalars.complexModule hA hW
    letI := rModule hA hV hW
    letI := lModule hA hV hW
    R hA hV hW →ₗ[ℂ] L hA hV hW :=
  @T A _ _ _ _ V _ _ W _ _ hA hV hW

example :
    letI := NondegenerateScalars.complexModule hA.op hV
    letI := NondegenerateScalars.complexModule hA hW
    letI := rModule hA hV hW
    letI := lModule hA hV hW
    L hA hV hW →ₗ[ℂ] R hA hV hW :=
  @S A _ _ _ _ V _ _ W _ _ hA hV hW

example :
    letI := rModule hA hV hW
    ∀ (c : ℂ) (φ : R hA hV hW) (v : V),
      ((c • φ) v).val = c • (φ v).val :=
  @rModule_smul_val A _ _ _ _ V _ _ W _ _ hA hV hW

example :
    letI := lModule hA hV hW
    ∀ (c : ℂ) (ψ : L hA hV hW) (w : W),
      ((c • ψ) w).val = c • (ψ w).val :=
  @lModule_smul_val A _ _ _ _ V _ _ W _ _ hA hV hW

end CompetingHomScalars

/-! Opposite-ring inputs explicitly retain the specified double-op and right actions. -/

section OppositeRing

variable {B : Type uA} [NonUnitalRing B] [Module ℂ B]
  [IsScalarTower ℂ B B] [SMulCommClass ℂ B B]
  {X : Type uV} [AddCommGroup X] [doubleOpAction : NonUnitalModule Bᵐᵒᵖᵐᵒᵖ X]
  {Y : Type uW} [AddCommGroup Y] [rightAction : NonUnitalModule Bᵐᵒᵖ Y]
  (hB : IsIdempotented B) (hX : IsNondegenerate Bᵐᵒᵖᵐᵒᵖ X)
  (hY : IsNondegenerate Bᵐᵒᵖ Y)

example :
    letI := doubleOpAction
    letI := rightAction
    letI := fullAction hB.op hY
    letI := fullAction hB.op.op hX
    letI := rightDualAction hB.op hX
    letI := rModule hB.op hX hY
    letI := lModule hB.op hX hY
    NonUnitalModuleHom Bᵐᵒᵖᵐᵒᵖ X (Dual hB.op hY) →ₗ[ℂ]
      NonUnitalModuleHom Bᵐᵒᵖ Y (Dual hB.op.op hX) :=
  @T Bᵐᵒᵖ _ _ _ _ X _ doubleOpAction Y _ rightAction hB.op hX hY

example :
    letI := doubleOpAction
    letI := rightAction
    letI := fullAction hB.op hY
    letI := fullAction hB.op.op hX
    letI := rightDualAction hB.op hX
    letI := rModule hB.op hX hY
    letI := lModule hB.op hX hY
    NonUnitalModuleHom Bᵐᵒᵖ Y (Dual hB.op.op hX) →ₗ[ℂ]
      NonUnitalModuleHom Bᵐᵒᵖᵐᵒᵖ X (Dual hB.op hY) :=
  @S Bᵐᵒᵖ _ _ _ _ X _ doubleOpAction Y _ rightAction hB.op hX hY

example :
    letI := fullAction hB.op.op hX
    letI := rightDualAction hB.op hX
    ∀ (b : Bᵐᵒᵖ) (ell : Dual hB.op.op hX),
      (b • ell).val = ell.val.comp
        (NondegenerateScalars.toLinearEndHom ℂ hB.op.op hX (op b)) :=
  @rightDualAction_val Bᵐᵒᵖ _ _ _ _ X _ doubleOpAction hB.op hX

end OppositeRing

/-! Both complete squares with competing original actions on all four carriers. -/

section CompetingNaturality

set_option linter.overlappingInstances false

variable {A : Type uA} [NonUnitalRing A] [Module ℂ A]
  [IsScalarTower ℂ A A] [SMulCommClass ℂ A A]
  {V : Type uV} [AddCommGroup V] [originalVAction : NonUnitalModule Aᵐᵒᵖ V]
  {W : Type uW} [AddCommGroup W] [originalWAction : NonUnitalModule A W]
  {V' : Type uV'} [AddCommGroup V'] [originalV'Action : NonUnitalModule Aᵐᵒᵖ V']
  {W' : Type uW'} [AddCommGroup W'] [originalW'Action : NonUnitalModule A W']
  (hA : IsIdempotented A) (hV : IsNondegenerate Aᵐᵒᵖ V)
  (hW : IsNondegenerate A W) (hV' : IsNondegenerate Aᵐᵒᵖ V')
  (hW' : IsNondegenerate A W')
  [competingVAction : NonUnitalModule Aᵐᵒᵖ V]
  [competingWAction : NonUnitalModule A W]
  [competingV'Action : NonUnitalModule Aᵐᵒᵖ V']
  [competingW'Action : NonUnitalModule A W']
  [competingVScalars : Module ℂ V] [competingWScalars : Module ℂ W]
  [competingV'Scalars : Module ℂ V'] [competingW'Scalars : Module ℂ W']

example :
    letI := originalVAction
    letI := originalWAction
    letI := originalV'Action
    letI := originalW'Action
    ∀ (_f : NonUnitalModuleHom Aᵐᵒᵖ V' V) (_g : NonUnitalModuleHom A W' W),
      R hA hV hW →+ R hA hV' hW' :=
  @Rfg A _ _ _ _ V _ originalVAction W _ originalWAction
    V' _ originalV'Action W' _ originalW'Action hA hV hW hV' hW'

example :
    letI := originalVAction
    letI := originalWAction
    letI := originalV'Action
    letI := originalW'Action
    ∀ (_f : NonUnitalModuleHom Aᵐᵒᵖ V' V) (_g : NonUnitalModuleHom A W' W),
      L hA hV hW →+ L hA hV' hW' :=
  @Lfg A _ _ _ _ V _ originalVAction W _ originalWAction
    V' _ originalV'Action W' _ originalW'Action hA hV hW hV' hW'

example :
    letI := originalVAction
    letI := originalWAction
    letI := originalV'Action
    letI := originalW'Action
    letI := NondegenerateScalars.complexModule hA.op hV
    letI := NondegenerateScalars.complexModule hA hW
    letI := NondegenerateScalars.complexModule hA.op hV'
    letI := NondegenerateScalars.complexModule hA hW'
    letI := rModule hA hV hW
    letI := lModule hA hV hW
    letI := rModule hA hV' hW'
    letI := lModule hA hV' hW'
    ∀ (f : NonUnitalModuleHom Aᵐᵒᵖ V' V) (g : NonUnitalModuleHom A W' W),
      (T hA hV' hW').toAddMonoidHom.comp (Rfg hA hV hW hV' hW' f g) =
        (Lfg hA hV hW hV' hW' f g).comp (T hA hV hW).toAddMonoidHom :=
  @T_natural A _ _ _ _ V _ originalVAction W _ originalWAction
    V' _ originalV'Action W' _ originalW'Action hA hV hW hV' hW'

example :
    letI := originalVAction
    letI := originalWAction
    letI := originalV'Action
    letI := originalW'Action
    letI := NondegenerateScalars.complexModule hA.op hV
    letI := NondegenerateScalars.complexModule hA hW
    letI := NondegenerateScalars.complexModule hA.op hV'
    letI := NondegenerateScalars.complexModule hA hW'
    letI := rModule hA hV hW
    letI := lModule hA hV hW
    letI := rModule hA hV' hW'
    letI := lModule hA hV' hW'
    ∀ (f : NonUnitalModuleHom Aᵐᵒᵖ V' V) (g : NonUnitalModuleHom A W' W),
      (S hA hV' hW').toAddMonoidHom.comp (Lfg hA hV hW hV' hW' f g) =
        (Rfg hA hV hW hV' hW' f g).comp (S hA hV hW).toAddMonoidHom :=
  @S_natural A _ _ _ _ V _ originalVAction W _ originalWAction
    V' _ originalV'Action W' _ originalW'Action hA hV hW hV' hW'

end CompetingNaturality

/-! Both squares specialize to the opposite ring with all actions selected. -/

section OppositeNaturality

variable {B : Type uA} [NonUnitalRing B] [Module ℂ B]
  [IsScalarTower ℂ B B] [SMulCommClass ℂ B B]
  {X : Type uV} [AddCommGroup X] [doubleOpX : NonUnitalModule Bᵐᵒᵖᵐᵒᵖ X]
  {Y : Type uW} [AddCommGroup Y] [rightY : NonUnitalModule Bᵐᵒᵖ Y]
  {X' : Type uV'} [AddCommGroup X'] [doubleOpX' : NonUnitalModule Bᵐᵒᵖᵐᵒᵖ X']
  {Y' : Type uW'} [AddCommGroup Y'] [rightY' : NonUnitalModule Bᵐᵒᵖ Y']
  (hB : IsIdempotented B) (hX : IsNondegenerate Bᵐᵒᵖᵐᵒᵖ X)
  (hY : IsNondegenerate Bᵐᵒᵖ Y) (hX' : IsNondegenerate Bᵐᵒᵖᵐᵒᵖ X')
  (hY' : IsNondegenerate Bᵐᵒᵖ Y')

example :
    letI := doubleOpX
    letI := rightY
    letI := doubleOpX'
    letI := rightY'
    letI := fullAction hB.op hY
    letI := fullAction hB.op hY'
    letI := fullAction hB.op.op hX
    letI := fullAction hB.op.op hX'
    letI := rightDualAction hB.op hX
    letI := rightDualAction hB.op hX'
    ∀ (f : NonUnitalModuleHom Bᵐᵒᵖᵐᵒᵖ X' X)
      (g : NonUnitalModuleHom Bᵐᵒᵖ Y' Y),
      (transposeAdd hB.op hX' hY').comp (Rfg hB.op hX hY hX' hY' f g) =
        (Lfg hB.op hX hY hX' hY' f g).comp (transposeAdd hB.op hX hY) :=
  @T_natural Bᵐᵒᵖ _ _ _ _ X _ doubleOpX Y _ rightY
    X' _ doubleOpX' Y' _ rightY' hB.op hX hY hX' hY'

example :
    letI := doubleOpX
    letI := rightY
    letI := doubleOpX'
    letI := rightY'
    letI := fullAction hB.op hY
    letI := fullAction hB.op hY'
    letI := fullAction hB.op.op hX
    letI := fullAction hB.op.op hX'
    letI := rightDualAction hB.op hX
    letI := rightDualAction hB.op hX'
    ∀ (f : NonUnitalModuleHom Bᵐᵒᵖᵐᵒᵖ X' X)
      (g : NonUnitalModuleHom Bᵐᵒᵖ Y' Y),
      (reverseAdd hB.op hX' hY').comp (Lfg hB.op hX hY hX' hY' f g) =
        (Rfg hB.op hX hY hX' hY' f g).comp (reverseAdd hB.op hX hY) :=
  @S_natural Bᵐᵒᵖ _ _ _ _ X _ doubleOpX Y _ rightY
    X' _ doubleOpX' Y' _ rightY' hB.op hX hY hX' hY'

end OppositeNaturality

/-! Concrete zero carriers with their original zero actions, in arbitrary universes. -/

section ZeroRightCarrier

variable {A : Type uA} [NonUnitalRing A] [Module ℂ A]
  [IsScalarTower ℂ A A] [SMulCommClass ℂ A A]
  {W : Type uW} [AddCommGroup W] [NonUnitalModule A W]
  (hA : IsIdempotented A) (hW : IsNondegenerate A W)

local instance : NonUnitalModule Aᵐᵒᵖ PUnit.{uV + 1} := NonUnitalModule.zero

example :
    let h0 : IsNondegenerate Aᵐᵒᵖ PUnit.{uV + 1} :=
      fun _ => ⟨⟨0, IsIdempotentElem.zero⟩, Subsingleton.elim _ _⟩
    letI := rModule hA h0 hW
    letI := lModule hA h0 hW
    R hA h0 hW →ₗ[ℂ] L hA h0 hW :=
  T hA (fun _ => ⟨⟨0, IsIdempotentElem.zero⟩, Subsingleton.elim _ _⟩) hW

example :
    let h0 : IsNondegenerate Aᵐᵒᵖ PUnit.{uV + 1} :=
      fun _ => ⟨⟨0, IsIdempotentElem.zero⟩, Subsingleton.elim _ _⟩
    letI := rModule hA h0 hW
    letI := lModule hA h0 hW
    L hA h0 hW →ₗ[ℂ] R hA h0 hW :=
  S hA (fun _ => ⟨⟨0, IsIdempotentElem.zero⟩, Subsingleton.elim _ _⟩) hW

end ZeroRightCarrier

section ZeroLeftCarrier

variable {A : Type uA} [NonUnitalRing A] [Module ℂ A]
  [IsScalarTower ℂ A A] [SMulCommClass ℂ A A]
  {V : Type uV} [AddCommGroup V] [NonUnitalModule Aᵐᵒᵖ V]
  (hA : IsIdempotented A) (hV : IsNondegenerate Aᵐᵒᵖ V)

local instance : NonUnitalModule A PUnit.{uW + 1} := NonUnitalModule.zero

example :
    let h0 : IsNondegenerate A PUnit.{uW + 1} :=
      fun _ => ⟨⟨0, IsIdempotentElem.zero⟩, Subsingleton.elim _ _⟩
    letI := rModule hA hV h0
    letI := lModule hA hV h0
    R hA hV h0 →ₗ[ℂ] L hA hV h0 :=
  T hA hV (fun _ => ⟨⟨0, IsIdempotentElem.zero⟩, Subsingleton.elim _ _⟩)

example :
    let h0 : IsNondegenerate A PUnit.{uW + 1} :=
      fun _ => ⟨⟨0, IsIdempotentElem.zero⟩, Subsingleton.elim _ _⟩
    letI := rModule hA hV h0
    letI := lModule hA hV h0
    L hA hV h0 →ₗ[ℂ] R hA hV h0 :=
  S hA hV (fun _ => ⟨⟨0, IsIdempotentElem.zero⟩, Subsingleton.elim _ _⟩)

end ZeroLeftCarrier

section ZeroAlgebraAndCarriers

local instance : NonUnitalModule PUnit.{uA + 1}ᵐᵒᵖ PUnit.{uV + 1} :=
  NonUnitalModule.zero
local instance : NonUnitalModule PUnit.{uA + 1} PUnit.{uW + 1} :=
  NonUnitalModule.zero

example :
    let h0A := IsIdempotented.of_ring PUnit.{uA + 1}
    let h0V : IsNondegenerate PUnit.{uA + 1}ᵐᵒᵖ PUnit.{uV + 1} :=
      fun _ => ⟨⟨0, IsIdempotentElem.zero⟩, Subsingleton.elim _ _⟩
    let h0W : IsNondegenerate PUnit.{uA + 1} PUnit.{uW + 1} :=
      fun _ => ⟨⟨0, IsIdempotentElem.zero⟩, Subsingleton.elim _ _⟩
    letI := rModule h0A h0V h0W
    letI := lModule h0A h0V h0W
    R h0A h0V h0W →ₗ[ℂ] L h0A h0V h0W :=
  T (IsIdempotented.of_ring PUnit.{uA + 1})
    (fun _ => ⟨⟨0, IsIdempotentElem.zero⟩, Subsingleton.elim _ _⟩)
    (fun _ => ⟨⟨0, IsIdempotentElem.zero⟩, Subsingleton.elim _ _⟩)

example :
    let h0A := IsIdempotented.of_ring PUnit.{uA + 1}
    let h0V : IsNondegenerate PUnit.{uA + 1}ᵐᵒᵖ PUnit.{uV + 1} :=
      fun _ => ⟨⟨0, IsIdempotentElem.zero⟩, Subsingleton.elim _ _⟩
    let h0W : IsNondegenerate PUnit.{uA + 1} PUnit.{uW + 1} :=
      fun _ => ⟨⟨0, IsIdempotentElem.zero⟩, Subsingleton.elim _ _⟩
    letI := rModule h0A h0V h0W
    letI := lModule h0A h0V h0W
    L h0A h0V h0W →ₗ[ℂ] R h0A h0V h0W :=
  S (IsIdempotented.of_ring PUnit.{uA + 1})
    (fun _ => ⟨⟨0, IsIdempotentElem.zero⟩, Subsingleton.elim _ _⟩)
    (fun _ => ⟨⟨0, IsIdempotentElem.zero⟩, Subsingleton.elim _ _⟩)

end ZeroAlgebraAndCarriers

end Langlands.Algebra.NonUnitalModuleDualHomTranspose
