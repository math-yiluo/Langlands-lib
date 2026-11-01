import Langlands.Algebra.RenardRegularCoefficientAdapters
import Mathlib.Algebra.Module.PUnit

/-!
# Interface checks for actual regular F/P coefficient comparisons

Complete theorem types, independent universes, competing named coefficient and
original-action structures, and zero and nonzero boundary applications.
-/

set_option autoImplicit false

namespace Langlands.Algebra.RenardRegularCoefficientAdaptersChecks

open MulOpposite
open RenardRegularCoefficientAdapters
open RenardRegularCoefficientStatements

universe uk uA uB

attribute [local instance] NondegenerateTensorScalars.opIsScalarTower
  NondegenerateTensorScalars.opSMulCommClass

noncomputable section

/-- The complete unapplied theorem has precisely the published target. -/
example : RegularCoefficientComparisons.{uk, uA, uB} :=
  regularCoefficientComparisons.{uk, uA, uB}

example : RegularCoefficientComparisons.{0, 1, 2} :=
  regularCoefficientComparisons.{0, 1, 2}

example : RegularCoefficientComparisons.{2, 1, 0} :=
  regularCoefficientComparisons.{2, 1, 0}

example : RegularCoefficientComparisons.{1, 0, 2} :=
  regularCoefficientComparisons.{1, 0, 2}

example : RegularCoefficientComparisons.{uk + 1, uA, uB} :=
  regularCoefficientComparisons.{uk + 1, uA, uB}

example : RegularCoefficientComparisons.{uk, uA + 1, uB} :=
  regularCoefficientComparisons.{uk, uA + 1, uB}

example : RegularCoefficientComparisons.{uk, uA, uB + 1} :=
  regularCoefficientComparisons.{uk, uA, uB + 1}

section CompleteHelperTypes

/-- The right-regular tower uses coefficient commutation alone. -/
example : ∀ (k : Type uk) {B : Type uB}
    [CommRing k] [NonUnitalRing B] [Module k B] [SMulCommClass k B B],
    letI := NonUnitalModule.rightRegular B
    IsScalarTower k Bᵐᵒᵖ B := @rightRegularTower

/-- Complete unapplied equality of the entire right-regular recovered Module. -/
example : ∀ (k : Type uk) {B : Type uB}
    [CommRing k] [NonUnitalRing B] [bCoefficients : Module k B]
    [IsScalarTower k B B] [SMulCommClass k B B] (hB : IsIdempotented B),
    letI := NonUnitalModule.rightRegular B
    NondegenerateTensorScalars.rightModule k hB
      (NondegenerateTensorFunctor.rightRegular_isNondegenerate hB) = bCoefficients :=
  @rightRegularRecoveredModule_eq

/-- Complete unapplied F compatibility, with no nondegeneracy assumption on A. -/
example : ∀ (k : Type uk) {B : Type uB}
    [CommRing k] [NonUnitalRing B] [Module k B]
    [IsScalarTower k B B] [SMulCommClass k B B]
    {A : Type uA} [NonUnitalRing A] [Module k A]
    [NonUnitalModule A B] [IsScalarTower k A B] (hB : IsIdempotented B),
    letI := NonUnitalModule.rightRegular B
    NonUnitalBimoduleTensorScalars.InputCompatible k (S := A) hB
      (NondegenerateTensorFunctor.rightRegular_isNondegenerate hB) := @fInputCompatible

/-- Complete unapplied supplied-right-action equality needs no B multiplication tower. -/
example : ∀ (k : Type uk) {A : Type uA} {B : Type uB}
    [CommRing k] [NonUnitalRing A] [NonUnitalRing B]
    [Module k A] [IsScalarTower k A A] [SMulCommClass k A A]
    [bCoefficients : Module k B] [NonUnitalModule Aᵐᵒᵖ B]
    [IsScalarTower k Aᵐᵒᵖ B] (hA : IsIdempotented A)
    (hRight : IsNondegenerate Aᵐᵒᵖ B),
    NondegenerateTensorScalars.rightModule k hA hRight = bCoefficients :=
  @rightActionRecoveredModule_eq

/-- Complete unapplied P compatibility needs only the stated half of B bilinearity. -/
example : ∀ (k : Type uk) {A : Type uA} {B : Type uB}
    [CommRing k] [NonUnitalRing A] [NonUnitalRing B]
    [Module k A] [IsScalarTower k A A] [SMulCommClass k A A]
    [Module k B] [NonUnitalModule Aᵐᵒᵖ B] [IsScalarTower k Aᵐᵒᵖ B]
    [IsScalarTower k B B] (hA : IsIdempotented A)
    (hRight : IsNondegenerate Aᵐᵒᵖ B),
    letI := NonUnitalModule.regular B
    NonUnitalBimoduleTensorScalars.InputCompatible k (S := B) hA hRight :=
  @pInputCompatible

end CompleteHelperTypes

section CompetingStructures

variable (k : Type uk) {A : Type uA} {B : Type uB}
  [CommRing k] [NonUnitalRing A] [NonUnitalRing B]
  (a0 a1 : Module k A) (b0 b1 : Module k B)
  (left0 left1 : NonUnitalModule A B)
  (right0 right1 : NonUnitalModule Aᵐᵒᵖ B)
  (regularLeftCompetitor : Unit → NonUnitalModule B B)
  (regularRightCompetitor : Unit → NonUnitalModule Bᵐᵒᵖ B)

/-- Recovery selects the named b0, and the exact right regular action, amid competitors. -/
example
    (bt0 : letI := b0; IsScalarTower k B B)
    (bc0 : letI := b0; SMulCommClass k B B) (hB : IsIdempotented B) :
    letI := b0
    letI := bt0
    letI := bc0
    RightRegularCoefficientComparison k hB := by
  let _ := b1
  let _ := regularRightCompetitor ()
  exact @rightRegularRecoveredModule_eq k B _ _ b0 bt0 bc0 hB

/-- F uses named coefficients and left action while selecting its own right regular action. -/
example
    (bt0 : letI := b0; IsScalarTower k B B)
    (bc0 : letI := b0; SMulCommClass k B B)
    (lt0 : letI := a0; letI := b0; letI := left0; IsScalarTower k A B)
    (hB : IsIdempotented B) :
    letI := a0
    letI := b0
    letI := bt0
    letI := bc0
    letI := left0
    letI := lt0
    FInputCompatibility (A := A) k hB := by
  let _ := a1
  let _ := b1
  let _ := left1
  let _ := regularRightCompetitor ()
  exact @fInputCompatible k B _ _ b0 bt0 bc0 A _ a0 left0 lt0 hB

/-- The supplied right action and named b0 survive a competing coefficient module and action. -/
example
    (at0 : letI := a0; IsScalarTower k A A)
    (ac0 : letI := a0; SMulCommClass k A A)
    (rt0 : letI := a0; letI := b0; letI := right0; IsScalarTower k Aᵐᵒᵖ B)
    (hA : IsIdempotented A)
    (hRight0 : letI := right0; IsNondegenerate Aᵐᵒᵖ B) :
    letI := a0
    letI := b0
    letI := at0
    letI := ac0
    letI := right0
    letI := rt0
    RightActionCoefficientComparison k hA hRight0 := by
  let _ := a1
  let _ := b1
  let _ := right1
  exact @rightActionRecoveredModule_eq k A B _ _ _ a0 at0 ac0 b0 right0 rt0 hA hRight0

/-- P selects the exact regular left action and the named supplied right action and coefficients. -/
example
    (at0 : letI := a0; IsScalarTower k A A)
    (ac0 : letI := a0; SMulCommClass k A A)
    (bt0 : letI := b0; IsScalarTower k B B)
    (rt0 : letI := a0; letI := b0; letI := right0; IsScalarTower k Aᵐᵒᵖ B)
    (hA : IsIdempotented A)
    (hRight0 : letI := right0; IsNondegenerate Aᵐᵒᵖ B) :
    letI := a0
    letI := b0
    letI := at0
    letI := ac0
    letI := bt0
    letI := right0
    letI := rt0
    PInputCompatibility k hA hRight0 := by
  let _ := a1
  let _ := b1
  let _ := right1
  let _ := regularLeftCompetitor ()
  exact @pInputCompatible k A B _ _ _ a0 at0 ac0 b0 right0 rt0 bt0 hA hRight0

end CompetingStructures

section RegularInteger

local instance : NonUnitalModule ℤ ℤ := NonUnitalModule.regular ℤ
local instance : NonUnitalModule ℤᵐᵒᵖ ℤ := NonUnitalModule.rightRegular ℤ

/-- All four conjuncts apply to the usual nonzero integer regular factors. -/
example :
    RightRegularCoefficientComparison ℤ (B := ℤ) (IsIdempotented.of_ring ℤ) ∧
    FInputCompatibility ℤ (A := ℤ) (B := ℤ) (IsIdempotented.of_ring ℤ) ∧
    RightActionCoefficientComparison ℤ (A := ℤ) (B := ℤ) (IsIdempotented.of_ring ℤ)
      (NondegenerateTensorFunctor.rightRegular_isNondegenerate (IsIdempotented.of_ring ℤ)) ∧
    PInputCompatibility ℤ (A := ℤ) (B := ℤ) (IsIdempotented.of_ring ℤ)
      (NondegenerateTensorFunctor.rightRegular_isNondegenerate (IsIdempotented.of_ring ℤ)) :=
  ⟨regularCoefficientComparisons.{0, 0, 0}.1 ℤ ℤ _,
    regularCoefficientComparisons.{0, 0, 0}.2.1 ℤ ℤ ℤ _,
    regularCoefficientComparisons.{0, 0, 0}.2.2.1 ℤ ℤ ℤ _ _,
    regularCoefficientComparisons.{0, 0, 0}.2.2.2 ℤ ℤ ℤ _ _⟩

/-- The recovered scalar action is nonzero, with 2 acting on 3 as 6. -/
example :
    (NondegenerateTensorScalars.rightModule ℤ (IsIdempotented.of_ring ℤ)
      (NondegenerateTensorFunctor.rightRegular_isNondegenerate
        (IsIdempotented.of_ring ℤ))).toSMul.smul 2 3 = 6 ∧ (6 : ℤ) ≠ 0 := by
  have hm := rightRegularRecoveredModule_eq ℤ (B := ℤ) (IsIdempotented.of_ring ℤ)
  have hc := congrArg (fun m : Module ℤ ℤ => m.toSMul.smul 2 3) hm
  constructor
  · exact hc.trans (show (2 : ℤ) • (3 : ℤ) = 6 by norm_num)
  · norm_num

end RegularInteger

section ZeroOriginalAction

local instance : NonUnitalModule (ℤ × ℤ) ℤ := NonUnitalModule.zero

local instance : IsScalarTower ℤ (ℤ × ℤ) ℤ where
  smul_assoc c _ _ := by
    change (0 : ℤ) = c • (0 : ℤ)
    exact (smul_zero c).symm

/-- F accepts a zero, degenerate original left action on a nonzero carrier. -/
example :
    FInputCompatibility ℤ (A := ℤ × ℤ) (B := ℤ) (IsIdempotented.of_ring ℤ) ∧
      ¬ IsNondegenerate (ℤ × ℤ) ℤ := by
  constructor
  · exact regularCoefficientComparisons.2.1 ℤ (ℤ × ℤ) ℤ _
  · intro h
    obtain ⟨e, he⟩ := h 1
    change (0 : ℤ) = 1 at he
    exact zero_ne_one he

end ZeroOriginalAction

section SubsingletonCarrier

variable (k : Type uk) {A : Type uA}
  [CommRing k] [NonUnitalRing A] [Module k A]
  [IsScalarTower k A A] [SMulCommClass k A A]

local instance : NonUnitalModule Aᵐᵒᵖ PUnit.{uB + 1} := NonUnitalModule.zero

local instance : IsScalarTower k Aᵐᵒᵖ PUnit.{uB + 1} :=
  ⟨fun _ _ _ => Subsingleton.elim _ _⟩

/-- A zero right action on a zero carrier is nondegenerate and admits both P comparisons. -/
example (hA : IsIdempotented A) :
    RightActionCoefficientComparison k (B := PUnit.{uB + 1}) hA
      NondegenerateTensorScalars.isNondegenerate_of_subsingleton ∧
    PInputCompatibility k (B := PUnit.{uB + 1}) hA
      NondegenerateTensorScalars.isNondegenerate_of_subsingleton :=
  ⟨regularCoefficientComparisons.2.2.1 k A PUnit hA _,
    regularCoefficientComparisons.2.2.2 k A PUnit hA _⟩

end SubsingletonCarrier

section ZeroCoefficientRing

local instance : NonUnitalModule PUnit.{1} PUnit.{1} := NonUnitalModule.regular PUnit
local instance : NonUnitalModule PUnit.{1}ᵐᵒᵖ PUnit.{1} := NonUnitalModule.rightRegular PUnit

/-- The coefficient ring and both algebras may all be the zero ring. -/
example :
    RightRegularCoefficientComparison PUnit.{1} (B := PUnit.{1}) (IsIdempotented.of_ring PUnit) ∧
    FInputCompatibility PUnit.{1} (A := PUnit.{1}) (B := PUnit.{1}) (IsIdempotented.of_ring PUnit) ∧
    RightActionCoefficientComparison PUnit.{1} (A := PUnit.{1}) (B := PUnit.{1})
      (IsIdempotented.of_ring PUnit)
      NondegenerateTensorScalars.isNondegenerate_of_subsingleton ∧
    PInputCompatibility PUnit.{1} (A := PUnit.{1}) (B := PUnit.{1}) (IsIdempotented.of_ring PUnit)
      NondegenerateTensorScalars.isNondegenerate_of_subsingleton :=
  ⟨regularCoefficientComparisons.{0, 0, 0}.1 PUnit PUnit _,
    regularCoefficientComparisons.{0, 0, 0}.2.1 PUnit PUnit PUnit _,
    regularCoefficientComparisons.{0, 0, 0}.2.2.1 PUnit PUnit PUnit _ _,
    regularCoefficientComparisons.{0, 0, 0}.2.2.2 PUnit PUnit PUnit _ _⟩

end ZeroCoefficientRing

/-! Additional supplied-structure checks contributed by Worker 1207. -/

/-- Exact unchanged target, with no additional parameters. -/
example : RegularCoefficientComparisons.{uk, uA, uB} :=
  @regularCoefficientComparisons.{uk, uA, uB}

/-- The coefficient ring can live below the two algebra universes. -/
example : RegularCoefficientComparisons.{0, 1, 2} :=
  @regularCoefficientComparisons.{0, 1, 2}

/-- The coefficient ring can also live above the two algebra universes. -/
example : RegularCoefficientComparisons.{2, 1, 0} :=
  @regularCoefficientComparisons.{2, 1, 0}

/-- Complete unapplied interface: exact right regular action and entire Module equality. -/
example : ∀ (k : Type uk) {B : Type uB}
    [CommRing k] [NonUnitalRing B] [bCoefficients : Module k B]
    [IsScalarTower k B B] [SMulCommClass k B B] (hB : IsIdempotented B),
    let _ := NonUnitalModule.rightRegular B
    NondegenerateTensorScalars.rightModule k hB
      (NondegenerateTensorFunctor.rightRegular_isNondegenerate hB) = bCoefficients :=
  @rightRegularRecoveredModule_eq

/-- Complete unapplied interface: the supplied left action and exact recovered coefficients. -/
example : ∀ (k : Type uk) {B : Type uB}
    [CommRing k] [NonUnitalRing B] [Module k B]
    [IsScalarTower k B B] [SMulCommClass k B B]
    {A : Type uA} [NonUnitalRing A] [Module k A]
    [NonUnitalModule A B] [IsScalarTower k A B] (hB : IsIdempotented B),
    let _ := NonUnitalModule.rightRegular B
    NonUnitalBimoduleTensorScalars.InputCompatible k (S := A) hB
      (NondegenerateTensorFunctor.rightRegular_isNondegenerate hB) :=
  @fInputCompatible

/-- Complete unapplied interface: the specified right action and its nondegeneracy witness. -/
example : ∀ (k : Type uk) {A : Type uA} {B : Type uB}
    [CommRing k] [NonUnitalRing A] [NonUnitalRing B]
    [Module k A] [IsScalarTower k A A] [SMulCommClass k A A]
    [bCoefficients : Module k B]
    [NonUnitalModule Aᵐᵒᵖ B] [IsScalarTower k Aᵐᵒᵖ B]
    (hA : IsIdempotented A) (hRight : IsNondegenerate Aᵐᵒᵖ B),
    NondegenerateTensorScalars.rightModule k hA hRight = bCoefficients :=
  @rightActionRecoveredModule_eq

/-- Complete unapplied interface: exact left regular action, with no commutation premise on B. -/
example : ∀ (k : Type uk) {A : Type uA} {B : Type uB}
    [CommRing k] [NonUnitalRing A] [NonUnitalRing B]
    [Module k A] [IsScalarTower k A A] [SMulCommClass k A A]
    [Module k B] [NonUnitalModule Aᵐᵒᵖ B] [IsScalarTower k Aᵐᵒᵖ B]
    [IsScalarTower k B B] (hA : IsIdempotented A)
    (hRight : IsNondegenerate Aᵐᵒᵖ B),
    let _ := NonUnitalModule.regular B
    NonUnitalBimoduleTensorScalars.InputCompatible k (S := B) hA hRight :=
  @pInputCompatible

section CompetingRegular

variable (k : Type uk) {B : Type uB}
  [kRing : CommRing k] [bRing : NonUnitalRing B]
  [bCoefficients : Module k B]
  [bTower : IsScalarTower k B B] [bComm : SMulCommClass k B B]

/-- Local competing coefficients and a competing original right action do not change the selection. -/
example (_otherCoefficients : Module k B) (_otherRight : NonUnitalModule Bᵐᵒᵖ B)
    (hB : IsIdempotented B) :
    @RightRegularCoefficientComparison k B kRing bRing bCoefficients bTower bComm hB := by
  let _ := _otherCoefficients
  let _ := _otherRight
  exact @rightRegularRecoveredModule_eq k B kRing bRing bCoefficients bTower bComm hB

variable {A : Type uA} [aRing : NonUnitalRing A] [aCoefficients : Module k A]
  [leftAction : NonUnitalModule A B] [leftTower : IsScalarTower k A B]

/-- F retains the supplied left action even when alternate left and right actions are local. -/
example (_otherCoefficients : Module k B) (_otherLeft : NonUnitalModule A B)
    (_otherRight : NonUnitalModule Bᵐᵒᵖ B) (hB : IsIdempotented B) :
    @FInputCompatibility k A B kRing aRing bRing aCoefficients bCoefficients
      bTower bComm leftAction leftTower hB := by
  let _ := _otherCoefficients
  let _ := _otherLeft
  let _ := _otherRight
  exact @fInputCompatible k B kRing bRing bCoefficients bTower bComm
    A aRing aCoefficients leftAction leftTower hB

end CompetingRegular

section CompetingRightAction

variable (k : Type uk) {A : Type uA} {B : Type uB}
  [kRing : CommRing k] [aRing : NonUnitalRing A] [bRing : NonUnitalRing B]
  [aCoefficients : Module k A]
  [aTower : IsScalarTower k A A] [aComm : SMulCommClass k A A]
  [bCoefficients : Module k B] [rightAction : NonUnitalModule Aᵐᵒᵖ B]
  [rightTower : IsScalarTower k Aᵐᵒᵖ B]

/-- The right-action comparison retains the named input Module and the specified original action. -/
example (_otherCoefficients : Module k B) (_otherRight : NonUnitalModule Aᵐᵒᵖ B)
    (hA : IsIdempotented A)
    (hRight : @IsNondegenerate Aᵐᵒᵖ B _ _ rightAction) :
    @RightActionCoefficientComparison k A B kRing aRing bRing aCoefficients aTower aComm
      bCoefficients rightAction rightTower hA hRight := by
  let _ := _otherCoefficients
  let _ := _otherRight
  exact @rightActionRecoveredModule_eq k A B kRing aRing bRing aCoefficients aTower aComm
    bCoefficients rightAction rightTower hA hRight

variable [bTower : IsScalarTower k B B]

/-- P retains its supplied right action and selects regular left multiplication over a competitor. -/
example (_otherCoefficients : Module k B) (_otherRight : NonUnitalModule Aᵐᵒᵖ B)
    (_otherLeft : NonUnitalModule B B)
    (hA : IsIdempotented A)
    (hRight : @IsNondegenerate Aᵐᵒᵖ B _ _ rightAction) :
    @PInputCompatibility k A B kRing aRing bRing aCoefficients aTower aComm
      bCoefficients bTower rightAction rightTower hA hRight := by
  let _ := _otherCoefficients
  let _ := _otherRight
  let _ := _otherLeft
  exact @pInputCompatible k A B kRing aRing bRing aCoefficients aTower aComm
    bCoefficients rightAction rightTower bTower hA hRight

end CompetingRightAction


end

end Langlands.Algebra.RenardRegularCoefficientAdaptersChecks
