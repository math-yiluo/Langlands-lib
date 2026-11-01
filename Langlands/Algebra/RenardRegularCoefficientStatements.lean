import Langlands.Algebra.NonUnitalBimoduleTensorScalars

/-!
# Actual regular-factor coefficient comparison statements

Derived sufficient-input infrastructure for Renard (9 July 2026), I.4.2.
These statements do not assert compatibility from original-action commutation.
-/

set_option autoImplicit false

namespace Langlands.Algebra.RenardRegularCoefficientStatements

open MulOpposite

universe uk uA uB

attribute [local instance] NondegenerateTensorScalars.opIsScalarTower
  NondegenerateTensorScalars.opSMulCommClass

/-- Recovery from the explicitly chosen right regular action returns B's given Module. -/
def RightRegularCoefficientComparison (k : Type uk) {B : Type uB}
    [CommRing k] [NonUnitalRing B] [bCoefficients : Module k B]
    [IsScalarTower k B B] [SMulCommClass k B B] (hB : IsIdempotented B) : Prop :=
  letI := NonUnitalModule.rightRegular B
  NondegenerateTensorScalars.rightModule k hB
    (NondegenerateTensorFunctor.rightRegular_isNondegenerate hB) = bCoefficients

/-- F's actual first factor satisfies the exact recovered-coefficient input law. -/
def FInputCompatibility (k : Type uk) {A : Type uA} {B : Type uB}
    [CommRing k] [NonUnitalRing A] [NonUnitalRing B]
    [Module k A] [Module k B] [IsScalarTower k B B] [SMulCommClass k B B]
    [NonUnitalModule A B] [IsScalarTower k A B] (hB : IsIdempotented B) : Prop :=
  letI := NonUnitalModule.rightRegular B
  NonUnitalBimoduleTensorScalars.InputCompatible k (S := A) hB
    (NondegenerateTensorFunctor.rightRegular_isNondegenerate hB)

/-- Recovery from a compatible nondegenerate original right A-action returns B's given Module. -/
def RightActionCoefficientComparison (k : Type uk) {A : Type uA} {B : Type uB}
    [CommRing k] [NonUnitalRing A] [NonUnitalRing B]
    [Module k A] [IsScalarTower k A A] [SMulCommClass k A A]
    [bCoefficients : Module k B] [NonUnitalModule Aᵐᵒᵖ B]
    [IsScalarTower k Aᵐᵒᵖ B] (hA : IsIdempotented A)
    (hRight : IsNondegenerate Aᵐᵒᵖ B) : Prop :=
  NondegenerateTensorScalars.rightModule k hA hRight = bCoefficients

/-- P's actual first factor satisfies the exact recovered-coefficient input law. -/
def PInputCompatibility (k : Type uk) {A : Type uA} {B : Type uB}
    [CommRing k] [NonUnitalRing A] [NonUnitalRing B]
    [Module k A] [IsScalarTower k A A] [SMulCommClass k A A]
    [Module k B] [IsScalarTower k B B] [NonUnitalModule Aᵐᵒᵖ B]
    [IsScalarTower k Aᵐᵒᵖ B] (hA : IsIdempotented A)
    (hRight : IsNondegenerate Aᵐᵒᵖ B) : Prop :=
  letI := NonUnitalModule.regular B
  NonUnitalBimoduleTensorScalars.InputCompatible k (S := B) hA hRight

/-- The four derived comparison families, with independent coefficient and algebra universes. -/
def RegularCoefficientComparisons : Prop :=
  (∀ (k : Type uk) (B : Type uB)
    [CommRing k] [NonUnitalRing B] [Module k B]
    [IsScalarTower k B B] [SMulCommClass k B B] (hB : IsIdempotented B),
    RightRegularCoefficientComparison k hB) ∧
  (∀ (k : Type uk) (A : Type uA) (B : Type uB)
    [CommRing k] [NonUnitalRing A] [NonUnitalRing B]
    [Module k A] [Module k B] [IsScalarTower k B B] [SMulCommClass k B B]
    [NonUnitalModule A B] [IsScalarTower k A B] (hB : IsIdempotented B),
    FInputCompatibility (A := A) k hB) ∧
  (∀ (k : Type uk) (A : Type uA) (B : Type uB)
    [CommRing k] [NonUnitalRing A] [NonUnitalRing B]
    [Module k A] [IsScalarTower k A A] [SMulCommClass k A A]
    [Module k B] [NonUnitalModule Aᵐᵒᵖ B] [IsScalarTower k Aᵐᵒᵖ B]
    (hA : IsIdempotented A) (hRight : IsNondegenerate Aᵐᵒᵖ B),
    RightActionCoefficientComparison k hA hRight) ∧
  (∀ (k : Type uk) (A : Type uA) (B : Type uB)
    [CommRing k] [NonUnitalRing A] [NonUnitalRing B]
    [Module k A] [IsScalarTower k A A] [SMulCommClass k A A]
    [Module k B] [IsScalarTower k B B] [NonUnitalModule Aᵐᵒᵖ B]
    [IsScalarTower k Aᵐᵒᵖ B] (hA : IsIdempotented A)
    (hRight : IsNondegenerate Aᵐᵒᵖ B),
    PInputCompatibility k hA hRight)

end Langlands.Algebra.RenardRegularCoefficientStatements
