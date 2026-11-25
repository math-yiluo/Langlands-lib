/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import Mathlib.Algebra.Field.ULift
public import Mathlib.CategoryTheory.Sites.Point.OfIsCofiltered
public import Mathlib.CategoryTheory.Sites.Point.Skyscraper
public import WeilConjectures.AlgebraicGeometry.CompletedIntegralCoefficients
public import WeilConjectures.AlgebraicGeometry.Morphisms.ProAffineEtale
public import WeilConjectures.AlgebraicGeometry.ProEtaleGeometricStalk
public import WeilConjectures.AlgebraicGeometry.ProEtaleWeaklyContractibleEvaluationColimits
public import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
public import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.WeaklyEtale
public import WeilConjectures.Mathlib.AlgebraicGeometry.Sites.Proetale
public import WeilConjectures.RingTheory.WContractibleGeometricCriterion

/-!
# Constant integral scalars with independent site and coefficient universes

Source: blueprint order 1455; Stacks Tag 03CO
(blueprint: def-weil-completed-integral-coefficients).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
universe t u
open CategoryTheory CategoryTheory.Limits Opposite
namespace WeilConjectures
variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E] (W : AlgebraicGeometry.Scheme.{t})

/-- The same constant coefficient sheaf, in the universe containing both inputs.
Source: blueprint order 1455 (blueprint: def-weil-completed-integral-coefficients). -/
abbrev integralConstantRingOfUniverses :
    Sheaf (AlgebraicGeometry.Scheme.ProEt.topology W) RingCat.{max u (t + 1)} :=
  (sheafCompose _ (forget₂ CommRingCat.{max u (t + 1)} RingCat.{max u (t + 1)})).obj
    ((constantSheaf _ CommRingCat.{max u (t + 1)}).obj
      (CommRingCat.of (ULift.{t + 1} (Padic.coefficientExtensionIntegers l E))))

/-- Constant sheafification of the actual quotient homomorphism.
Source: blueprint order 1455 (blueprint: def-weil-completed-integral-coefficients). -/
def integralConstantQuotientOfUniverses (n : ℕ) :
    integralConstantRingOfUniverses l E W ⟶ integralCoefficientSheaf l E W n :=
  (sheafCompose _ (forget₂ CommRingCat.{max u (t + 1)} RingCat.{max u (t + 1)})).map
    ((constantSheaf _ CommRingCat.{max u (t + 1)}).map
      (CommRingCat.ofHom
        ((ULift.ringEquiv : ULift.{t + 1} _ ≃+* _).symm.toRingHom.comp
          ((Ideal.Quotient.mk (Padic.coefficientExtensionIdeal l E (n + 1))).comp
            (ULift.ringEquiv : ULift.{t + 1} _ ≃+* _).toRingHom))))

/-- Consecutive quotients commute with the constant-scalar maps.
Source: blueprint order 1455 (blueprint: def-weil-completed-integral-coefficients).
Proof: quotient induction identifies both ring homomorphisms with the quotient at n+1;
constant sheafification and forgetting commutativity preserve that equality. -/
theorem integralConstantQuotientOfUniverses_compatibility (n : ℕ) :
    ((Functor.const ℕᵒᵖ).obj (integralConstantRingOfUniverses l E W)).map
        (homOfLE (Nat.le_succ n)).op ≫ integralConstantQuotientOfUniverses l E W n =
      integralConstantQuotientOfUniverses l E W (n + 1) ≫
        (integralCoefficientSheafSystem l E W).map (homOfLE (Nat.le_succ n)).op := by
  simp only [Functor.const_obj_map, integralCoefficientSheafSystem,
    Functor.ofOpSequence_map_homOfLE_succ]
  unfold integralConstantQuotientOfUniverses integralCoefficientSheafTransition
  rw [← Functor.map_comp, ← Functor.map_comp]
  congr 2

/-- The cone of constant scalars, with its actual finite quotient legs.
Source: blueprint order 1455 (blueprint: def-weil-completed-integral-coefficients). -/
def integralConstantConeOfUniverses : Cone (integralCoefficientSheafSystem l E W) :=
  { pt := integralConstantRingOfUniverses l E W
    π := NatTrans.ofOpSequence (integralConstantQuotientOfUniverses l E W)
      (integralConstantQuotientOfUniverses_compatibility l E W) }

/-- The canonical constant-to-completed map is the limit lift of the quotient cone.
Source: blueprint order 1455 (blueprint: def-weil-completed-integral-coefficients). -/
def integralConstantToCompletionOfUniverses :
    integralConstantRingOfUniverses l E W ⟶ completedIntegralCoefficientSheafUnrestricted l E W :=
  limit.lift _ (integralConstantConeOfUniverses l E W)

end WeilConjectures
