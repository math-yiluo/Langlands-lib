import Langlands.Algebra.RenardRegularCoefficientStatements

/-!
# Coefficient comparisons for the actual regular F/P factors

Derived adapters for the sufficient common-coefficient interpretation
of Renard (9 July 2026), I.4.2. This does not close the source convention issue.
-/

set_option autoImplicit false

namespace Langlands.Algebra.RenardRegularCoefficientAdapters

open MulOpposite

universe uk uA uB

attribute [local instance] NondegenerateTensorScalars.opIsScalarTower
  NondegenerateTensorScalars.opSMulCommClass

section RightRegular

variable (k : Type uk) {B : Type uB}
  [CommRing k] [NonUnitalRing B] [bCoefficients : Module k B]
  [IsScalarTower k B B] [SMulCommClass k B B]

local instance regularRight : NonUnitalModule Bᵐᵒᵖ B := NonUnitalModule.rightRegular B

omit [IsScalarTower k B B] in
/-- The coefficient tower for the explicitly chosen original right regular action. -/
theorem rightRegularTower : IsScalarTower k Bᵐᵒᵖ B := by
  refine ⟨fun c b x => ?_⟩
  change x * (c • b.unop) = c • (x * b.unop)
  exact mul_smul_comm c x b.unop

/-- Recovery from right multiplication returns the supplied coefficients on B. -/
theorem rightRegularRecoveredModule_eq (hB : IsIdempotented B) :
    NondegenerateTensorScalars.rightModule k hB
      (NondegenerateTensorFunctor.rightRegular_isNondegenerate hB) = bCoefficients := by
  let _ := rightRegularTower k (B := B)
  exact NondegenerateScalars.module_eq_of_compatible k hB.op
    (NondegenerateTensorFunctor.rightRegular_isNondegenerate hB)

variable {A : Type uA} [NonUnitalRing A] [Module k A]
  [NonUnitalModule A B] [IsScalarTower k A B]

/-- The actual F factor satisfies InputCompatible for its exact right-recovered coefficients. -/
theorem fInputCompatible (hB : IsIdempotented B) :
    NonUnitalBimoduleTensorScalars.InputCompatible k (S := A) hB
      (NondegenerateTensorFunctor.rightRegular_isNondegenerate hB) := by
  unfold NonUnitalBimoduleTensorScalars.InputCompatible
  rw [rightRegularRecoveredModule_eq k hB]
  infer_instance

end RightRegular

section RightAction

variable (k : Type uk) {A : Type uA} {B : Type uB}
  [CommRing k] [NonUnitalRing A] [NonUnitalRing B]
  [Module k A] [IsScalarTower k A A] [SMulCommClass k A A]
  [bCoefficients : Module k B]
  [NonUnitalModule Aᵐᵒᵖ B] [IsScalarTower k Aᵐᵒᵖ B]

/-- Recovery from the supplied compatible nondegenerate right A-action returns B's coefficients. -/
theorem rightActionRecoveredModule_eq (hA : IsIdempotented A)
    (hRight : IsNondegenerate Aᵐᵒᵖ B) :
    NondegenerateTensorScalars.rightModule k hA hRight = bCoefficients := by
  exact NondegenerateScalars.module_eq_of_compatible k hA.op hRight

variable [IsScalarTower k B B]

local instance regularLeft : NonUnitalModule B B := NonUnitalModule.regular B

/-- The actual P factor satisfies InputCompatible for its exact right-A-recovered coefficients. -/
theorem pInputCompatible (hA : IsIdempotented A)
    (hRight : IsNondegenerate Aᵐᵒᵖ B) :
    NonUnitalBimoduleTensorScalars.InputCompatible k (S := B) hA hRight := by
  unfold NonUnitalBimoduleTensorScalars.InputCompatible
  rw [rightActionRecoveredModule_eq k hA hRight]
  exact ⟨fun c b x => smul_mul_assoc c b x⟩

end RightAction

/-- Proof of all four statement families; no comparison map or output certificate is an input. -/
theorem regularCoefficientComparisons :
    RenardRegularCoefficientStatements.RegularCoefficientComparisons.{uk, uA, uB} := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro k B _ _ _ _ _ hB
    exact rightRegularRecoveredModule_eq k hB
  · intro k A B _ _ _ _ _ _ _ _ _ hB
    exact fInputCompatible (A := A) k hB
  · intro k A B _ _ _ _ _ _ _ _ _ hA hRight
    exact rightActionRecoveredModule_eq k hA hRight
  · intro k A B _ _ _ _ _ _ _ _ _ _ hA hRight
    exact pInputCompatible k hA hRight

end Langlands.Algebra.RenardRegularCoefficientAdapters
