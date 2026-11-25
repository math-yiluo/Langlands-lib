/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.InternalPerfectOrdinaryReductions
import WeilConjectures.AlgebraicGeometry.InternalPerfectReductionHomEquiv

/-! # Chain-level form of successor counit naturality -/

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

/-- Representative-level successor counit naturality.

Source: the counit naturality step of `def-pe-internal-perfect-reduction-hom-equiv`.
(blueprint: lem-pe-internal-perfect-ordinary-step-counit-chain).

Proof: apply `internalPerfectOrdinaryStepCounit_naturality` (naturality of the derived
extension counit, conjugated by ordinary balancing) to the homotopy class of `g`, then
expand the ordinary balancing step of that class as the conjugated chain map
(`internalPerfectOrdinaryHomStep_map`). -/
theorem internalPerfectOrdinaryStepCounit_chain
    (W : Scheme.{u})
    (P : CochainComplex (ModuleCat.{u} (Padic.coefficientExtensionIntegers l E)) ℤ)
    (n : ℕ)
    (g : internalPerfectOrdinaryReduction l E W P (n + 1) ⟶
      internalPerfectOrdinaryReduction l E W P (n + 1)) :
    let F := Mod.extendScalars (AdicCompletion.transition l E W n)
    let H := HomotopyCategory.quotient
      (Mod (Sheaf (Scheme.ProEt.topology W) Ab.{u + 1})
        (AdicCompletion.finiteRing l E W n)) (.up ℤ)
    let H₁ := HomotopyCategory.quotient
      (Mod (Sheaf (Scheme.ProEt.topology W) Ab.{u + 1})
        (AdicCompletion.finiteRing l E W (n + 1))) (.up ℤ)
    let a := internalPerfectOrdinaryReductionStep l E W P n
    let ε := F.leftDerivedFunctorCounit.app (H₁.obj
      (internalPerfectOrdinaryReduction l E W P (n + 1)))
    let s := a.inv ≫
      (F.mapHomologicalComplex (.up ℤ)).map g ≫ a.hom
    F.leftDerivedFunctor.map (DerivedCategory.Qh.map (H₁.map g)) ≫ ε ≫
        DerivedCategory.Qh.map (H.map a.hom) =
      ε ≫ DerivedCategory.Qh.map (H.map a.hom) ≫
        DerivedCategory.Qh.map (H.map s) := by
  intro F H H₁ a ε s
  have h := internalPerfectOrdinaryStepCounit_naturality l E W P n (H₁.map g)
  rw [internalPerfectOrdinaryHomStep_map] at h
  exact h

end AlgebraicGeometry.ProEtale
