/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.InternalPerfectOrdinaryReductions
import all WeilConjectures.AlgebraicGeometry.FiniteConstantModel.FiniteConstantModelResolutionSupplement
import WeilConjectures.CategoryTheory.ModuleObjects.ExtendScalars
import Mathlib.LinearAlgebra.Dimension.Free

/-! # Finite-free terms of the explicit ordinary reductions -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits MonoidalCategory Opposite
namespace AlgebraicGeometry.ProEtale

attribute [local instance] AdicCompletion.ringMonoidalObject AdicCompletion.ringCommutative
  AdicCompletion.finiteRingMonoidalObject AdicCompletion.finiteRingCommutative

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]

/-- Every term of the ordinary quotient complex is a finite sum of the regular module.
No boundedness or weak contractibility is needed for this termwise assertion.
Source: Stacks Tag 09C6, finite-free scalar reduction.
(blueprint: lem-pe-internal-perfect-ordinary-terms-free).

Proof: choose a finite basis in the scalar module and lift it to the coefficient universe.
The constant scalar realization identifies the corresponding finite power with the same
finite sum of the regular integral module. Ordinary quotient extension preserves this sum
and takes the regular integral module to the regular finite quotient module. -/
theorem internalPerfectOrdinaryReduction_terms_free (W : Scheme.{u})
    (P : CochainComplex (ModuleCat.{u} (Padic.coefficientExtensionIntegers l E)) ℤ)
    (hfree : ∀ i : ℤ, Module.Finite (Padic.coefficientExtensionIntegers l E) (P.X i) ∧
      Module.Free (Padic.coefficientExtensionIntegers l E) (P.X i))
    (n : ℕ) (i : ℤ) :
    ∃ r : ℕ, Nonempty ((internalPerfectOrdinaryReduction l E W P n).X i ≅
      Mod.finiteFree (AdicCompletion.finiteRing l E W n) r) := by
  let := (Padic.coefficientExtensionAbsoluteValue l E).toNormedField
  let A := Padic.coefficientExtensionIntegers l E
  let : Module.Finite A (P.X i) := (hfree i).1
  let : Module.Free A (P.X i) := (hfree i).2
  let M := (ModuleCat.uliftFunctor.{u + 1, u} A).obj (P.X i)
  have : Module.Free A M := by
    change Module.Free A (ULift.{u + 1} (P.X i))
    infer_instance
  have : Module.Finite A M := by
    change Module.Finite A (ULift.{u + 1} (P.X i))
    infer_instance
  let r := Module.finrank A M
  let e : M ≅ FiniteConstantModel.freeScalars A r :=
    ((Module.finBasis A M).equivFun.trans
      (LinearEquiv.piCongrRight (fun _ : Fin r ↦ ULift.moduleEquiv.symm))).toModuleIso
  obtain ⟨b⟩ := FiniteConstantModel.modelFiniteFree A W r
  let F := Mod.extendScalars (AdicCompletion.quotient l E W n)
  refine ⟨r, ⟨?_⟩⟩
  exact F.mapIso ((FiniteConstantModel.modelFunctor A W).mapIso e ≪≫ b) ≪≫
    F.mapBiproduct (fun _ : Fin r ↦ Mod.regular (AdicCompletion.ring l E W)) ≪≫
      biproduct.mapIso (fun _ ↦ Mod.regularExtensionIso (AdicCompletion.quotient l E W n))

end AlgebraicGeometry.ProEtale
