/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.AdicCompletion.DerivedCompletionSupplement
import WeilConjectures.CategoryTheory.ModuleObjects.DerivedExtendScalarsComp
import Mathlib.RingTheory.Ideal.Quotient.Operations

/-! # Canonical residue normalization for native integral reductions
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits MonoidalCategory MonObj
open scoped CategoryTheory.Obj
namespace AlgebraicGeometry.ProEtale

attribute [local irreducible] upperStarFromPoint
attribute [local instance] AdicCompletion.ringMonoidalObject AdicCompletion.ringCommutative
  AdicCompletion.finiteRingMonoidalObject AdicCompletion.finiteRingCommutative
  AdicCompletion.modulesMonoidal AdicCompletion.modulesSymmetric AdicCompletion.modulesClosed
  AdicCompletion.modulesMonoidalPreadditive AdicCompletion.finiteModulesDerived
  AdicCompletion.modulesDerived

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E] (X : Scheme.{u})

/-- The actual composite from a positive finite level to the first quotient. -/
def integralResidueTransition : ∀ n : ℕ,
    AdicCompletion.finiteRing l E X n ⟶ AdicCompletion.finiteRing l E X 0
  | 0 => 𝟙 _
  | n + 1 => AdicCompletion.transition l E X n ≫ integralResidueTransition n

/-- Composites of quotient ring maps preserve multiplication and the unit. -/
instance integralResidueTransition_isMonHom (n : ℕ) :
    IsMonHom (integralResidueTransition l E X n) := by
  induction n with
  | zero => dsimp [integralResidueTransition]; infer_instance
  | succ n ih => dsimp only [integralResidueTransition]; infer_instance

/-- The composite integral quotient and residue map is the first quotient. -/
theorem integralResidueTransition_quotient (n : ℕ) :
    AdicCompletion.quotient l E X n ≫ integralResidueTransition l E X n =
      AdicCompletion.quotient l E X 0 := by
  induction n with
  | zero => simp [integralResidueTransition]
  | succ n ih =>
    rw [integralResidueTransition, ← Category.assoc,
      AdicCompletion.quotient_transition, ih]

/-- The residue quotient used by the etale Tor test is the actual first finite ring.
Construction: the image of the principal uniformizer ideal is the principal ideal of
its image. The third isomorphism theorem, since its positive power lies inside it,
identifies the further quotient with the first coefficient quotient. -/
def integralResidueQuotientEquiv (n : ℕ) :
    (Padic.coefficientExtensionRing l E (n + 1) ⧸
      Ideal.span ({(Ideal.Quotient.mk (Padic.coefficientExtensionIdeal l E (n + 1))
        (Padic.coefficientExtensionUniformizer l E))} :
        Set (Padic.coefficientExtensionRing l E (n + 1)))) ≃+*
      Padic.coefficientExtensionRing l E 1 := by
  let J := Ideal.span ({Padic.coefficientExtensionUniformizer l E} :
    Set (Padic.coefficientExtensionIntegers l E))
  have he : Ideal.span ({(Ideal.Quotient.mk (J ^ (n + 1))
      (Padic.coefficientExtensionUniformizer l E))} :
      Set (Padic.coefficientExtensionIntegers l E ⧸ J ^ (n + 1))) =
      J.map (Ideal.Quotient.mk (J ^ (n + 1))) := by
    dsimp only [J]
    rw [Ideal.map_span, Set.image_singleton]
  change (_ ⧸ _) ≃+* (_ ⧸ J ^ 1)
  exact (Ideal.quotEquivOfEq he).trans
    ((DoubleQuot.quotQuotEquivQuotOfLE (Ideal.pow_le_self (by omega))).trans
      (Ideal.quotEquivOfEq (pow_one J).symm))

/-- The residue quotient identification preserves every original integral scalar. -/
theorem integralResidueQuotientEquiv_mk (n : ℕ)
    (a : Padic.coefficientExtensionIntegers l E) :
    integralResidueQuotientEquiv l E n
      (Ideal.Quotient.mk _
        (Ideal.Quotient.mk (Padic.coefficientExtensionIdeal l E (n + 1)) a)) =
      Ideal.Quotient.mk (Padic.coefficientExtensionIdeal l E 1) a := by
  rfl

/-- Derived scalar extension of a native finite reduction to the residue quotient is
canonically isomorphic to the first native reduction. -/
theorem integral_finite_residue_normalization
    (K : DerivedCategory (AdicCompletion.Modules l E X)) (n : ℕ) :
    Nonempty ((Mod.extendScalars (integralResidueTransition l E X n)).leftDerivedFunctor.obj
      ((AdicCompletion.derivedReduction l E X n).obj K) ≅
        (AdicCompletion.derivedReduction l E X 0).obj K) := by
  exact ⟨((Mod.derivedExtendScalarsCompIso (AdicCompletion.quotient l E X n)
    (integralResidueTransition l E X n) (AdicCompletion.quotient l E X 0)
    (integralResidueTransition_quotient l E X n)).app K).symm⟩

end AlgebraicGeometry.ProEtale
