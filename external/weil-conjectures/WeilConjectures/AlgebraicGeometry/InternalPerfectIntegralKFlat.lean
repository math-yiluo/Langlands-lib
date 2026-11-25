/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.InternalPerfectOrdinaryReductions
public import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.KFlat
import all WeilConjectures.AlgebraicGeometry.FiniteConstantModel.FiniteConstantModelResolutionSupplement
import Mathlib.LinearAlgebra.Dimension.Free

/-! # K-flatness of the explicit integral scalar model -/

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

/-- The explicit integral realization of a bounded finite-free complex is K-flat.
Source: Stacks Tag 06YY.
(blueprint: lem-pe-internal-perfect-integral-kflat).

Proof: a lifted finite basis identifies every term with a finite biproduct of the
regular integral module, the tensor unit. Tensoring with this unit is exact, and
finite coproducts of flat objects are flat because finite coproducts are exact.
The additive realization preserves the two strict bounds. The bounded flat-complex
criterion gives K-flatness. Neither weak contractibility nor nonemptiness is used. -/
theorem internalPerfectIntegralComplex_kflat (W : Scheme.{u})
    (P : CochainComplex (ModuleCat.{u} (Padic.coefficientExtensionIntegers l E)) ℤ)
    (a b : ℤ) (ha : P.IsStrictlyGE a) (hb : P.IsStrictlyLE b)
    (hfree : ∀ i : ℤ, Module.Finite (Padic.coefficientExtensionIntegers l E) (P.X i) ∧
      Module.Free (Padic.coefficientExtensionIntegers l E) (P.X i)) :
    (HomologicalComplex.quasiIso (AdicCompletion.Modules l E W) (.up ℤ)).kFlat
      (internalPerfectIntegralComplex l E W P) := by
  let := (Padic.coefficientExtensionAbsoluteValue l E).toNormedField
  let A := Padic.coefficientExtensionIntegers l E
  let C := AdicCompletion.Modules l E W
  let := ha
  let := hb
  have : CochainComplex.IsStrictlyGE (internalPerfectIntegralComplex l E W P) a := by
    unfold internalPerfectIntegralComplex
    infer_instance
  have : CochainComplex.IsStrictlyLE (internalPerfectIntegralComplex l E W P) b := by
    unfold internalPerfectIntegralComplex
    infer_instance
  apply CochainComplex.kFlat_of_bounded_of_flat _ a b
  intro i
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
  obtain ⟨c⟩ := FiniteConstantModel.modelFiniteFree A W r
  let b := (FiniteConstantModel.modelFunctor A W).mapIso e ≪≫ c
  apply ObjectProperty.prop_of_iso ObjectProperty.flat b.symm
  have : (ObjectProperty.flat (A := C)).IsClosedUnderColimitsOfShape (Discrete (Fin r)) :=
    CochainComplex.closedUnderColimitsOfShape_flat C _
  apply ObjectProperty.prop_of_isColimit ObjectProperty.flat (biproduct.isColimit _)
  intro j
  exact ObjectProperty.prop_unit ObjectProperty.flat

end AlgebraicGeometry.ProEtale
