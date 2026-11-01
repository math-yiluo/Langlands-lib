import Langlands.Algebra.NonUnitalTensorAssociativityStatements

/-!
# Checks for the original balanced tensor associativity interfaces

These are internal interface and boundary checks, not proofs of the associator
or its naturality. See the paired Markdown for scope and provenance.
-/

set_option autoImplicit false

namespace Langlands.Algebra.NonUnitalTensorAssociativityChecks

open MulOpposite NonUnitalTensorAssociativity
open NonUnitalModuleTensor (Tensor tmul lift IsBalanced)
open NonUnitalBimoduleTensor (rightModule leftModule)

universe uR uS uX uY uZ uX' uY' uZ'

/-! Each complete telescope is checked against the unapplied declaration. -/
section Interfaces
set_option linter.unusedVariables false

example : ∀ (R : Type uR) (S : Type uS) (X : Type uX) (Y : Type uY) (Z : Type uZ)
    [NonUnitalRing R] [NonUnitalRing S]
    [AddCommGroup X] [AddCommGroup Y] [AddCommGroup Z]
    [NonUnitalModule Rᵐᵒᵖ X] [NonUnitalModule R Y]
    [NonUnitalModule Sᵐᵒᵖ Y] [NonUnitalModule S Z]
    (hY : ActionsCommute R S Y),
    (LeftTensor R S X Y Z hY ≃+ RightTensor R S X Y Z hY) → Prop := @PureTensorFormulas

example : ∀ (R : Type uR) (S : Type uS) (X : Type uX) (Y : Type uY) (Z : Type uZ)
    [NonUnitalRing R] [NonUnitalRing S]
    [AddCommGroup X] [AddCommGroup Y] [AddCommGroup Z]
    [NonUnitalModule Rᵐᵒᵖ X] [NonUnitalModule R Y]
    [NonUnitalModule Sᵐᵒᵖ Y] [NonUnitalModule S Z]
    (hY : ActionsCommute R S Y),
    (LeftTensor R S X Y Z hY ≃+ RightTensor R S X Y Z hY) → Prop := @NestedLiftFormulas

example : ∀ (R : Type uR) (S : Type uS) (X : Type uX) (Y : Type uY) (Z : Type uZ)
    [NonUnitalRing R] [NonUnitalRing S]
    [AddCommGroup X] [AddCommGroup Y] [AddCommGroup Z]
    [NonUnitalModule Rᵐᵒᵖ X] [NonUnitalModule R Y]
    [NonUnitalModule Sᵐᵒᵖ Y] [NonUnitalModule S Z]
    (hY : ActionsCommute R S Y),
    (LeftTensor R S X Y Z hY ≃+ RightTensor R S X Y Z hY) → Prop := @InverseIdentities

example : ∀ (R : Type uR) (S : Type uS) (X : Type uX) (Y : Type uY) (Z : Type uZ)
    [NonUnitalRing R] [NonUnitalRing S]
    [AddCommGroup X] [AddCommGroup Y] [AddCommGroup Z]
    [NonUnitalModule Rᵐᵒᵖ X] [NonUnitalModule R Y]
    [NonUnitalModule Sᵐᵒᵖ Y] [NonUnitalModule S Z]
    (hY : ActionsCommute R S Y),
    (LeftTensor R S X Y Z hY ≃+ RightTensor R S X Y Z hY) → Prop := @Canonical

example : ∀ (R : Type uR) (S : Type uS) (X : Type uX) (Y : Type uY) (Z : Type uZ)
    [NonUnitalRing R] [NonUnitalRing S]
    [AddCommGroup X] [AddCommGroup Y] [AddCommGroup Z]
    [NonUnitalModule Rᵐᵒᵖ X] [NonUnitalModule R Y]
    [NonUnitalModule Sᵐᵒᵖ Y] [NonUnitalModule S Z]
    (hY : ActionsCommute R S Y), Prop := @ExistsCanonical

example : ∀ (R : Type uR) (S : Type uS)
    (X : Type uX) (Y : Type uY) (Z : Type uZ)
    (X' : Type uX') (Y' : Type uY') (Z' : Type uZ')
    [NonUnitalRing R] [NonUnitalRing S]
    [AddCommGroup X] [AddCommGroup Y] [AddCommGroup Z]
    [AddCommGroup X'] [AddCommGroup Y'] [AddCommGroup Z']
    [NonUnitalModule Rᵐᵒᵖ X] [NonUnitalModule R Y]
    [NonUnitalModule Sᵐᵒᵖ Y] [NonUnitalModule S Z]
    [NonUnitalModule Rᵐᵒᵖ X'] [NonUnitalModule R Y']
    [NonUnitalModule Sᵐᵒᵖ Y'] [NonUnitalModule S Z']
    (hY : ActionsCommute R S Y) (hY' : ActionsCommute R S Y'), Prop := @Naturality

example : Prop := NonUnitalTensorAssociativityTheorem.{uR, uS, uX, uY, uZ, uX', uY', uZ'}

/-! First unequal assignment, in order R, S, X, Y, Z, X', Y', Z'. -/

example : ∀ (R : Type 0) (S : Type 1) (X : Type 0) (Y : Type 1) (Z : Type 0)
    [NonUnitalRing R] [NonUnitalRing S]
    [AddCommGroup X] [AddCommGroup Y] [AddCommGroup Z]
    [NonUnitalModule Rᵐᵒᵖ X] [NonUnitalModule R Y]
    [NonUnitalModule Sᵐᵒᵖ Y] [NonUnitalModule S Z]
    (hY : ActionsCommute R S Y),
    (LeftTensor R S X Y Z hY ≃+ RightTensor R S X Y Z hY) → Prop := @PureTensorFormulas

example : ∀ (R : Type 0) (S : Type 1) (X : Type 0) (Y : Type 1) (Z : Type 0)
    [NonUnitalRing R] [NonUnitalRing S]
    [AddCommGroup X] [AddCommGroup Y] [AddCommGroup Z]
    [NonUnitalModule Rᵐᵒᵖ X] [NonUnitalModule R Y]
    [NonUnitalModule Sᵐᵒᵖ Y] [NonUnitalModule S Z]
    (hY : ActionsCommute R S Y),
    (LeftTensor R S X Y Z hY ≃+ RightTensor R S X Y Z hY) → Prop := @NestedLiftFormulas

example : ∀ (R : Type 0) (S : Type 1) (X : Type 0) (Y : Type 1) (Z : Type 0)
    [NonUnitalRing R] [NonUnitalRing S]
    [AddCommGroup X] [AddCommGroup Y] [AddCommGroup Z]
    [NonUnitalModule Rᵐᵒᵖ X] [NonUnitalModule R Y]
    [NonUnitalModule Sᵐᵒᵖ Y] [NonUnitalModule S Z]
    (hY : ActionsCommute R S Y),
    (LeftTensor R S X Y Z hY ≃+ RightTensor R S X Y Z hY) → Prop := @InverseIdentities

example : ∀ (R : Type 0) (S : Type 1) (X : Type 0) (Y : Type 1) (Z : Type 0)
    [NonUnitalRing R] [NonUnitalRing S]
    [AddCommGroup X] [AddCommGroup Y] [AddCommGroup Z]
    [NonUnitalModule Rᵐᵒᵖ X] [NonUnitalModule R Y]
    [NonUnitalModule Sᵐᵒᵖ Y] [NonUnitalModule S Z]
    (hY : ActionsCommute R S Y),
    (LeftTensor R S X Y Z hY ≃+ RightTensor R S X Y Z hY) → Prop := @Canonical

example : ∀ (R : Type 0) (S : Type 1) (X : Type 0) (Y : Type 1) (Z : Type 0)
    [NonUnitalRing R] [NonUnitalRing S]
    [AddCommGroup X] [AddCommGroup Y] [AddCommGroup Z]
    [NonUnitalModule Rᵐᵒᵖ X] [NonUnitalModule R Y]
    [NonUnitalModule Sᵐᵒᵖ Y] [NonUnitalModule S Z]
    (hY : ActionsCommute R S Y), Prop := @ExistsCanonical

example : ∀ (R : Type 0) (S : Type 1)
    (X : Type 0) (Y : Type 1) (Z : Type 0)
    (X' : Type 1) (Y' : Type 0) (Z' : Type 1)
    [NonUnitalRing R] [NonUnitalRing S]
    [AddCommGroup X] [AddCommGroup Y] [AddCommGroup Z]
    [AddCommGroup X'] [AddCommGroup Y'] [AddCommGroup Z']
    [NonUnitalModule Rᵐᵒᵖ X] [NonUnitalModule R Y]
    [NonUnitalModule Sᵐᵒᵖ Y] [NonUnitalModule S Z]
    [NonUnitalModule Rᵐᵒᵖ X'] [NonUnitalModule R Y']
    [NonUnitalModule Sᵐᵒᵖ Y'] [NonUnitalModule S Z']
    (hY : ActionsCommute R S Y) (hY' : ActionsCommute R S Y'), Prop := @Naturality

example : Prop := NonUnitalTensorAssociativityTheorem.{0, 1, 0, 1, 0, 1, 0, 1}

/-! Reversed unequal assignment, in order R, S, X, Y, Z, X', Y', Z'. -/

example : ∀ (R : Type 1) (S : Type 0) (X : Type 1) (Y : Type 0) (Z : Type 1)
    [NonUnitalRing R] [NonUnitalRing S]
    [AddCommGroup X] [AddCommGroup Y] [AddCommGroup Z]
    [NonUnitalModule Rᵐᵒᵖ X] [NonUnitalModule R Y]
    [NonUnitalModule Sᵐᵒᵖ Y] [NonUnitalModule S Z]
    (hY : ActionsCommute R S Y),
    (LeftTensor R S X Y Z hY ≃+ RightTensor R S X Y Z hY) → Prop := @PureTensorFormulas

example : ∀ (R : Type 1) (S : Type 0) (X : Type 1) (Y : Type 0) (Z : Type 1)
    [NonUnitalRing R] [NonUnitalRing S]
    [AddCommGroup X] [AddCommGroup Y] [AddCommGroup Z]
    [NonUnitalModule Rᵐᵒᵖ X] [NonUnitalModule R Y]
    [NonUnitalModule Sᵐᵒᵖ Y] [NonUnitalModule S Z]
    (hY : ActionsCommute R S Y),
    (LeftTensor R S X Y Z hY ≃+ RightTensor R S X Y Z hY) → Prop := @NestedLiftFormulas

example : ∀ (R : Type 1) (S : Type 0) (X : Type 1) (Y : Type 0) (Z : Type 1)
    [NonUnitalRing R] [NonUnitalRing S]
    [AddCommGroup X] [AddCommGroup Y] [AddCommGroup Z]
    [NonUnitalModule Rᵐᵒᵖ X] [NonUnitalModule R Y]
    [NonUnitalModule Sᵐᵒᵖ Y] [NonUnitalModule S Z]
    (hY : ActionsCommute R S Y),
    (LeftTensor R S X Y Z hY ≃+ RightTensor R S X Y Z hY) → Prop := @InverseIdentities

example : ∀ (R : Type 1) (S : Type 0) (X : Type 1) (Y : Type 0) (Z : Type 1)
    [NonUnitalRing R] [NonUnitalRing S]
    [AddCommGroup X] [AddCommGroup Y] [AddCommGroup Z]
    [NonUnitalModule Rᵐᵒᵖ X] [NonUnitalModule R Y]
    [NonUnitalModule Sᵐᵒᵖ Y] [NonUnitalModule S Z]
    (hY : ActionsCommute R S Y),
    (LeftTensor R S X Y Z hY ≃+ RightTensor R S X Y Z hY) → Prop := @Canonical

example : ∀ (R : Type 1) (S : Type 0) (X : Type 1) (Y : Type 0) (Z : Type 1)
    [NonUnitalRing R] [NonUnitalRing S]
    [AddCommGroup X] [AddCommGroup Y] [AddCommGroup Z]
    [NonUnitalModule Rᵐᵒᵖ X] [NonUnitalModule R Y]
    [NonUnitalModule Sᵐᵒᵖ Y] [NonUnitalModule S Z]
    (hY : ActionsCommute R S Y), Prop := @ExistsCanonical

example : ∀ (R : Type 1) (S : Type 0)
    (X : Type 1) (Y : Type 0) (Z : Type 1)
    (X' : Type 0) (Y' : Type 1) (Z' : Type 0)
    [NonUnitalRing R] [NonUnitalRing S]
    [AddCommGroup X] [AddCommGroup Y] [AddCommGroup Z]
    [AddCommGroup X'] [AddCommGroup Y'] [AddCommGroup Z']
    [NonUnitalModule Rᵐᵒᵖ X] [NonUnitalModule R Y]
    [NonUnitalModule Sᵐᵒᵖ Y] [NonUnitalModule S Z]
    [NonUnitalModule Rᵐᵒᵖ X'] [NonUnitalModule R Y']
    [NonUnitalModule Sᵐᵒᵖ Y'] [NonUnitalModule S Z']
    (hY : ActionsCommute R S Y) (hY' : ActionsCommute R S Y'), Prop := @Naturality

example : Prop := NonUnitalTensorAssociativityTheorem.{1, 0, 1, 0, 1, 0, 1, 0}

end Interfaces

/-! Exact unfolding checks retain both whole-map lifts and both naturality squares. -/

section Unfolding

variable (R : Type uR) (S : Type uS)
  (X : Type uX) (Y : Type uY) (Z : Type uZ)
  (X' : Type uX') (Y' : Type uY') (Z' : Type uZ')
  [NonUnitalRing R] [NonUnitalRing S]
  [AddCommGroup X] [AddCommGroup Y] [AddCommGroup Z]
  [AddCommGroup X'] [AddCommGroup Y'] [AddCommGroup Z']
  [NonUnitalModule Rᵐᵒᵖ X] [NonUnitalModule R Y]
  [NonUnitalModule Sᵐᵒᵖ Y] [NonUnitalModule S Z]
  [NonUnitalModule Rᵐᵒᵖ X'] [NonUnitalModule R Y']
  [NonUnitalModule Sᵐᵒᵖ Y'] [NonUnitalModule S Z']
  (hY : ActionsCommute R S Y) (hY' : ActionsCommute R S Y')

example (E : LeftTensor R S X Y Z hY ≃+ RightTensor R S X Y Z hY) :
    PureTensorFormulas R S X Y Z hY E =
      (letI := rightModule X hY
       letI := leftModule hY Z
       (∀ (x : X) (y : Y) (z : Z),
         E (tmul S (Tensor R X Y) Z (tmul R X Y x y) z) =
           tmul R X (Tensor S Y Z) x (tmul S Y Z y z)) ∧
       (∀ (x : X) (y : Y) (z : Z),
         E.symm (tmul R X (Tensor S Y Z) x (tmul S Y Z y z)) =
           tmul S (Tensor R X Y) Z (tmul R X Y x y) z)) := rfl

example (E : LeftTensor R S X Y Z hY ≃+ RightTensor R S X Y Z hY) :
    NestedLiftFormulas R S X Y Z hY E =
      (letI := rightModule X hY
       letI := leftModule hY Z
       E.toAddMonoidHom =
           lift S (forwardPairing R S X Y Z hY) (forwardPairing_balanced R S X Y Z hY) ∧
       E.symm.toAddMonoidHom =
           lift R (inversePairing R S X Y Z hY) (inversePairing_balanced R S X Y Z hY)) := rfl

example (E : LeftTensor R S X Y Z hY ≃+ RightTensor R S X Y Z hY) :
    InverseIdentities R S X Y Z hY E =
      (E.symm.toAddMonoidHom.comp E.toAddMonoidHom =
          AddMonoidHom.id (LeftTensor R S X Y Z hY) ∧
       E.toAddMonoidHom.comp E.symm.toAddMonoidHom =
          AddMonoidHom.id (RightTensor R S X Y Z hY)) := rfl

example (E : LeftTensor R S X Y Z hY ≃+ RightTensor R S X Y Z hY) :
    Canonical R S X Y Z hY E =
      (PureTensorFormulas R S X Y Z hY E ∧
       NestedLiftFormulas R S X Y Z hY E ∧ InverseIdentities R S X Y Z hY E) := rfl

example : ExistsCanonical R S X Y Z hY =
    (∃ E : LeftTensor R S X Y Z hY ≃+ RightTensor R S X Y Z hY,
      Canonical R S X Y Z hY E) := rfl

example : Naturality R S X Y Z X' Y' Z' hY hY' =
    (∀ (E : LeftTensor R S X Y Z hY ≃+ RightTensor R S X Y Z hY)
       (E' : LeftTensor R S X' Y' Z' hY' ≃+ RightTensor R S X' Y' Z' hY'),
       Canonical R S X Y Z hY E → Canonical R S X' Y' Z' hY' E' →
       ∀ (f : NonUnitalModuleHom Rᵐᵒᵖ X X')
         (g : NonUnitalBimoduleHom R S Y Y') (k : NonUnitalModuleHom S Z Z'),
         letI := rightModule X hY
         letI := rightModule X' hY'
         letI := leftModule hY Z
         letI := leftModule hY' Z'
         let ML := NonUnitalModuleTensor.map S (NonUnitalBimoduleTensor.rightMap hY hY' f g) k
         let MR := NonUnitalModuleTensor.map R f (NonUnitalBimoduleTensor.leftMap hY hY' g k)
         E'.toAddMonoidHom.comp ML = MR.comp E.toAddMonoidHom ∧
           E'.symm.toAddMonoidHom.comp MR = ML.comp E.symm.toAddMonoidHom) := rfl

/-- The evaluation maps and their inner lifts are the stated actual pairings. -/
example (x : X) (y : Y) (z : Z) :
    forwardInner R S X Y Z hY z x y =
      (letI := leftModule hY Z
       tmul R X (Tensor S Y Z) x (tmul S Y Z y z)) := rfl

example (z : Z) : forwardAt R S X Y Z hY z =
    lift R (forwardInner R S X Y Z hY z) (forwardInner_balanced R S X Y Z hY z) := rfl

example (t : Tensor R X Y) (z : Z) :
    forwardPairing R S X Y Z hY t z = forwardAt R S X Y Z hY z t := rfl

example (x : X) (y : Y) (z : Z) :
    inverseInner R S X Y Z hY x y z =
      (letI := rightModule X hY
       tmul S (Tensor R X Y) Z (tmul R X Y x y) z) := rfl

example (x : X) : inverseAt R S X Y Z hY x =
    lift S (inverseInner R S X Y Z hY x) (inverseInner_balanced R S X Y Z hY x) := rfl

example (x : X) (u : Tensor S Y Z) :
    inversePairing R S X Y Z hY x u = inverseAt R S X Y Z hY x u := rfl

end Unfolding

/-! The closed target has no inputs, and supplies both universe-sized families. -/

example : NonUnitalTensorAssociativityTheorem.{uR, uS, uX, uY, uZ, uX', uY', uZ'} =
    ((∀ (R : Type uR) (S : Type uS) (X : Type uX) (Y : Type uY) (Z : Type uZ)
    [NonUnitalRing R] [NonUnitalRing S]
    [AddCommGroup X] [AddCommGroup Y] [AddCommGroup Z]
    [NonUnitalModule Rᵐᵒᵖ X] [NonUnitalModule R Y]
    [NonUnitalModule Sᵐᵒᵖ Y] [NonUnitalModule S Z]
    (hY : ActionsCommute R S Y), ExistsCanonical R S X Y Z hY) ∧
    (∀ (R : Type uR) (S : Type uS) (X : Type uX') (Y : Type uY') (Z : Type uZ')
    [NonUnitalRing R] [NonUnitalRing S]
    [AddCommGroup X] [AddCommGroup Y] [AddCommGroup Z]
    [NonUnitalModule Rᵐᵒᵖ X] [NonUnitalModule R Y]
    [NonUnitalModule Sᵐᵒᵖ Y] [NonUnitalModule S Z]
    (hY : ActionsCommute R S Y),
      ExistsCanonical R S X Y Z hY) ∧
    (∀ (R : Type uR) (S : Type uS)
    (X : Type uX) (Y : Type uY) (Z : Type uZ)
    (X' : Type uX') (Y' : Type uY') (Z' : Type uZ')
    [NonUnitalRing R] [NonUnitalRing S]
    [AddCommGroup X] [AddCommGroup Y] [AddCommGroup Z]
    [AddCommGroup X'] [AddCommGroup Y'] [AddCommGroup Z']
    [NonUnitalModule Rᵐᵒᵖ X] [NonUnitalModule R Y]
    [NonUnitalModule Sᵐᵒᵖ Y] [NonUnitalModule S Z]
    [NonUnitalModule Rᵐᵒᵖ X'] [NonUnitalModule R Y']
    [NonUnitalModule Sᵐᵒᵖ Y'] [NonUnitalModule S Z']
    (hY : ActionsCommute R S Y) (hY' : ActionsCommute R S Y'), Naturality R S X Y Z X' Y' Z' hY hY')) := rfl

example : NonUnitalTensorAssociativityTheorem.{0, 1, 0, 1, 0, 1, 0, 1} =
    ((∀ (R : Type 0) (S : Type 1) (X : Type 0) (Y : Type 1) (Z : Type 0)
    [NonUnitalRing R] [NonUnitalRing S]
    [AddCommGroup X] [AddCommGroup Y] [AddCommGroup Z]
    [NonUnitalModule Rᵐᵒᵖ X] [NonUnitalModule R Y]
    [NonUnitalModule Sᵐᵒᵖ Y] [NonUnitalModule S Z]
    (hY : ActionsCommute R S Y), ExistsCanonical R S X Y Z hY) ∧
    (∀ (R : Type 0) (S : Type 1) (X : Type 1) (Y : Type 0) (Z : Type 1)
    [NonUnitalRing R] [NonUnitalRing S]
    [AddCommGroup X] [AddCommGroup Y] [AddCommGroup Z]
    [NonUnitalModule Rᵐᵒᵖ X] [NonUnitalModule R Y]
    [NonUnitalModule Sᵐᵒᵖ Y] [NonUnitalModule S Z]
    (hY : ActionsCommute R S Y),
      ExistsCanonical R S X Y Z hY) ∧
    (∀ (R : Type 0) (S : Type 1)
    (X : Type 0) (Y : Type 1) (Z : Type 0)
    (X' : Type 1) (Y' : Type 0) (Z' : Type 1)
    [NonUnitalRing R] [NonUnitalRing S]
    [AddCommGroup X] [AddCommGroup Y] [AddCommGroup Z]
    [AddCommGroup X'] [AddCommGroup Y'] [AddCommGroup Z']
    [NonUnitalModule Rᵐᵒᵖ X] [NonUnitalModule R Y]
    [NonUnitalModule Sᵐᵒᵖ Y] [NonUnitalModule S Z]
    [NonUnitalModule Rᵐᵒᵖ X'] [NonUnitalModule R Y']
    [NonUnitalModule Sᵐᵒᵖ Y'] [NonUnitalModule S Z']
    (hY : ActionsCommute R S Y) (hY' : ActionsCommute R S Y'), Naturality R S X Y Z X' Y' Z' hY hY')) := rfl

example : NonUnitalTensorAssociativityTheorem.{1, 0, 1, 0, 1, 0, 1, 0} =
    ((∀ (R : Type 1) (S : Type 0) (X : Type 1) (Y : Type 0) (Z : Type 1)
    [NonUnitalRing R] [NonUnitalRing S]
    [AddCommGroup X] [AddCommGroup Y] [AddCommGroup Z]
    [NonUnitalModule Rᵐᵒᵖ X] [NonUnitalModule R Y]
    [NonUnitalModule Sᵐᵒᵖ Y] [NonUnitalModule S Z]
    (hY : ActionsCommute R S Y), ExistsCanonical R S X Y Z hY) ∧
    (∀ (R : Type 1) (S : Type 0) (X : Type 0) (Y : Type 1) (Z : Type 0)
    [NonUnitalRing R] [NonUnitalRing S]
    [AddCommGroup X] [AddCommGroup Y] [AddCommGroup Z]
    [NonUnitalModule Rᵐᵒᵖ X] [NonUnitalModule R Y]
    [NonUnitalModule Sᵐᵒᵖ Y] [NonUnitalModule S Z]
    (hY : ActionsCommute R S Y),
      ExistsCanonical R S X Y Z hY) ∧
    (∀ (R : Type 1) (S : Type 0)
    (X : Type 1) (Y : Type 0) (Z : Type 1)
    (X' : Type 0) (Y' : Type 1) (Z' : Type 0)
    [NonUnitalRing R] [NonUnitalRing S]
    [AddCommGroup X] [AddCommGroup Y] [AddCommGroup Z]
    [AddCommGroup X'] [AddCommGroup Y'] [AddCommGroup Z']
    [NonUnitalModule Rᵐᵒᵖ X] [NonUnitalModule R Y]
    [NonUnitalModule Sᵐᵒᵖ Y] [NonUnitalModule S Z]
    [NonUnitalModule Rᵐᵒᵖ X'] [NonUnitalModule R Y']
    [NonUnitalModule Sᵐᵒᵖ Y'] [NonUnitalModule S Z']
    (hY : ActionsCommute R S Y) (hY' : ActionsCommute R S Y'), Naturality R S X Y Z X' Y' Z' hY hY')) := rfl

/-! Original structures remain fixed while instance search selects competing ones. -/

section CompetingStructures
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

variable (R : Type uR) (S : Type uS)
  (X : Type uX) (Y : Type uY) (Z : Type uZ)
  (X' : Type uX') (Y' : Type uY') (Z' : Type uZ')
  (r₀ : NonUnitalRing R) [r₁ : NonUnitalRing R]
  (s₀ : NonUnitalRing S) [s₁ : NonUnitalRing S]
  (gx₀ : AddCommGroup X) [gx₁ : AddCommGroup X]
  (gy₀ : AddCommGroup Y) [gy₁ : AddCommGroup Y]
  (gz₀ : AddCommGroup Z) [gz₁ : AddCommGroup Z]
  (gx'₀ : AddCommGroup X') [gx'₁ : AddCommGroup X']
  (gy'₀ : AddCommGroup Y') [gy'₁ : AddCommGroup Y']
  (gz'₀ : AddCommGroup Z') [gz'₁ : AddCommGroup Z']
  (xR₀ : letI := r₀; @NonUnitalModule Rᵐᵒᵖ X _ gx₀)
  (yR₀ : @NonUnitalModule R Y r₀ gy₀)
  (yS₀ : letI := s₀; @NonUnitalModule Sᵐᵒᵖ Y _ gy₀)
  (zS₀ : @NonUnitalModule S Z s₀ gz₀)
  (hY : @ActionsCommute R S Y r₀ s₀ gy₀ yR₀ yS₀)
  [xR₁ : letI := r₁; @NonUnitalModule Rᵐᵒᵖ X _ gx₁]
  [yR₁ : @NonUnitalModule R Y r₁ gy₁]
  [yS₁ : letI := s₁; @NonUnitalModule Sᵐᵒᵖ Y _ gy₁]
  [zS₁ : @NonUnitalModule S Z s₁ gz₁]
  (xR'₀ : letI := r₀; @NonUnitalModule Rᵐᵒᵖ X' _ gx'₀)
  (yR'₀ : @NonUnitalModule R Y' r₀ gy'₀)
  (yS'₀ : letI := s₀; @NonUnitalModule Sᵐᵒᵖ Y' _ gy'₀)
  (zS'₀ : @NonUnitalModule S Z' s₀ gz'₀)
  (hY' : @ActionsCommute R S Y' r₀ s₀ gy'₀ yR'₀ yS'₀)
  [xR'₁ : letI := r₁; @NonUnitalModule Rᵐᵒᵖ X' _ gx'₁]
  [yR'₁ : @NonUnitalModule R Y' r₁ gy'₁]
  [yS'₁ : letI := s₁; @NonUnitalModule Sᵐᵒᵖ Y' _ gy'₁]
  [zS'₁ : @NonUnitalModule S Z' s₁ gz'₁]

local notation "Q" => @Tensor R X Y r₀ gx₀ gy₀ xR₀ yR₀
local notation "V" => @Tensor S Y Z s₀ gy₀ gz₀ yS₀ zS₀
local notation "GQ" => @NonUnitalModuleTensor.addCommGroup R X Y r₀ gx₀ gy₀ xR₀ yR₀
local notation "GV" => @NonUnitalModuleTensor.addCommGroup S Y Z s₀ gy₀ gz₀ yS₀ zS₀
local notation "AQ" => @rightModule R S r₀ s₀ X gx₀ xR₀ Y gy₀ yR₀ yS₀ hY
local notation "AV" => @leftModule R S r₀ s₀ Y gy₀ yR₀ yS₀ hY Z gz₀ zS₀
local notation "L" => @LeftTensor R S X Y Z r₀ s₀ gx₀ gy₀ gz₀ xR₀ yR₀ yS₀ zS₀ hY
local notation "T" => @RightTensor R S X Y Z r₀ s₀ gx₀ gy₀ gz₀ xR₀ yR₀ yS₀ zS₀ hY
local notation "GL" => @leftTensorGroup R S X Y Z r₀ s₀ gx₀ gy₀ gz₀ xR₀ yR₀ yS₀ zS₀ hY
local notation "GT" => @rightTensorGroup R S X Y Z r₀ s₀ gx₀ gy₀ gz₀ xR₀ yR₀ yS₀ zS₀ hY

variable [gq₁ : AddCommGroup Q] [gv₁ : AddCommGroup V]
  [qS₁ : letI := s₁; @NonUnitalModule Sᵐᵒᵖ Q _ gq₁]
  [vR₁ : @NonUnitalModule R V r₁ gv₁]
  [gl₁ : AddCommGroup L] [gt₁ : AddCommGroup T]

local notation "Q'" => @Tensor R X' Y' r₀ gx'₀ gy'₀ xR'₀ yR'₀
local notation "V'" => @Tensor S Y' Z' s₀ gy'₀ gz'₀ yS'₀ zS'₀
local notation "GQ'" => @NonUnitalModuleTensor.addCommGroup R X' Y' r₀ gx'₀ gy'₀ xR'₀ yR'₀
local notation "GV'" => @NonUnitalModuleTensor.addCommGroup S Y' Z' s₀ gy'₀ gz'₀ yS'₀ zS'₀
local notation "AQ'" => @rightModule R S r₀ s₀ X' gx'₀ xR'₀ Y' gy'₀ yR'₀ yS'₀ hY'
local notation "AV'" => @leftModule R S r₀ s₀ Y' gy'₀ yR'₀ yS'₀ hY' Z' gz'₀ zS'₀
local notation "L'" => @LeftTensor R S X' Y' Z' r₀ s₀ gx'₀ gy'₀ gz'₀ xR'₀ yR'₀ yS'₀ zS'₀ hY'
local notation "T'" => @RightTensor R S X' Y' Z' r₀ s₀ gx'₀ gy'₀ gz'₀ xR'₀ yR'₀ yS'₀ zS'₀ hY'
local notation "GL'" => @leftTensorGroup R S X' Y' Z' r₀ s₀ gx'₀ gy'₀ gz'₀ xR'₀ yR'₀ yS'₀ zS'₀ hY'
local notation "GT'" => @rightTensorGroup R S X' Y' Z' r₀ s₀ gx'₀ gy'₀ gz'₀ xR'₀ yR'₀ yS'₀ zS'₀ hY'

variable [gq'₁ : AddCommGroup Q'] [gv'₁ : AddCommGroup V']
  [qS'₁ : letI := s₁; @NonUnitalModule Sᵐᵒᵖ Q' _ gq'₁]
  [vR'₁ : @NonUnitalModule R V' r₁ gv'₁]
  [gl'₁ : AddCommGroup L'] [gt'₁ : AddCommGroup T']

include r₁ s₁ gx₁ gy₁ gz₁ gx'₁ gy'₁ gz'₁ xR₁ yR₁ yS₁ zS₁ xR'₁ yR'₁ yS'₁ zS'₁
include gq₁ gv₁ qS₁ vR₁ gl₁ gt₁ gq'₁ gv'₁ qS'₁ vR'₁ gl'₁ gt'₁

example : (inferInstance : NonUnitalRing R) = r₁ := rfl
example : (inferInstance : NonUnitalRing S) = s₁ := rfl
example : (inferInstance : AddCommGroup X) = gx₁ := rfl
example : (inferInstance : AddCommGroup Y) = gy₁ := rfl
example : (inferInstance : AddCommGroup Z) = gz₁ := rfl
example : (inferInstance : AddCommGroup X') = gx'₁ := rfl
example : (inferInstance : AddCommGroup Y') = gy'₁ := rfl
example : (inferInstance : AddCommGroup Z') = gz'₁ := rfl
example : (inferInstance : NonUnitalModule Rᵐᵒᵖ X) = xR₁ := rfl
example : (inferInstance : NonUnitalModule R Y) = yR₁ := rfl
example : (inferInstance : NonUnitalModule Sᵐᵒᵖ Y) = yS₁ := rfl
example : (inferInstance : NonUnitalModule S Z) = zS₁ := rfl
private theorem competingGroup1 : (inferInstance : AddCommGroup Q) = gq₁ := rfl
private theorem competingGroup2 : (inferInstance : AddCommGroup V) = gv₁ := rfl
private theorem competingGroup3 : (inferInstance : AddCommGroup L) = gl₁ := rfl
private theorem competingGroup4 : (inferInstance : AddCommGroup T) = gt₁ := rfl
private theorem competingAction9 : (inferInstance : @NonUnitalModule Sᵐᵒᵖ Q
    (by letI := s₁; infer_instance) gq₁) = qS₁ := rfl
private theorem competingAction10 : (inferInstance : @NonUnitalModule R V r₁ gv₁) = vR₁ := rfl

example : L = @Tensor S Q Z s₀ GQ gz₀ AQ zS₀ := rfl
example : T = @Tensor R X V r₀ gx₀ GV xR₀ AV := rfl
example : GL = @NonUnitalModuleTensor.addCommGroup S Q Z s₀ GQ gz₀ AQ zS₀ := rfl
example : GT = @NonUnitalModuleTensor.addCommGroup R X V r₀ gx₀ GV xR₀ AV := rfl

example : (inferInstance : NonUnitalModule Rᵐᵒᵖ X') = xR'₁ := rfl
example : (inferInstance : NonUnitalModule R Y') = yR'₁ := rfl
example : (inferInstance : NonUnitalModule Sᵐᵒᵖ Y') = yS'₁ := rfl
example : (inferInstance : NonUnitalModule S Z') = zS'₁ := rfl
private theorem competingGroup5 : (inferInstance : AddCommGroup Q') = gq'₁ := rfl
private theorem competingGroup6 : (inferInstance : AddCommGroup V') = gv'₁ := rfl
private theorem competingGroup7 : (inferInstance : AddCommGroup L') = gl'₁ := rfl
private theorem competingGroup8 : (inferInstance : AddCommGroup T') = gt'₁ := rfl
private theorem competingAction11 : (inferInstance : @NonUnitalModule Sᵐᵒᵖ Q'
    (by letI := s₁; infer_instance) gq'₁) = qS'₁ := rfl
private theorem competingAction12 : (inferInstance : @NonUnitalModule R V' r₁ gv'₁) = vR'₁ := rfl

example : L' = @Tensor S Q' Z' s₀ GQ' gz'₀ AQ' zS'₀ := rfl
example : T' = @Tensor R X' V' r₀ gx'₀ GV' xR'₀ AV' := rfl
example : GL' = @NonUnitalModuleTensor.addCommGroup S Q' Z' s₀ GQ' gz'₀ AQ' zS'₀ := rfl
example : GT' = @NonUnitalModuleTensor.addCommGroup R X' V' r₀ gx'₀ GV' xR'₀ AV' := rfl

/-- Both evaluation pairings use the original groups, tensors and residual actions. -/
example (x : X) (y : Y) (z : Z) :
    @forwardInner R S X Y Z r₀ s₀ gx₀ gy₀ gz₀ xR₀ yR₀ yS₀ zS₀ hY z x y =
      @tmul R X V r₀ gx₀ GV xR₀ AV x (@tmul S Y Z s₀ gy₀ gz₀ yS₀ zS₀ y z) := rfl

example (x : X) (y : Y) (z : Z) :
    @inverseInner R S X Y Z r₀ s₀ gx₀ gy₀ gz₀ xR₀ yR₀ yS₀ zS₀ hY x y z =
      @tmul S Q Z s₀ GQ gz₀ AQ zS₀ (@tmul R X Y r₀ gx₀ gy₀ xR₀ yR₀ x y) z := rfl

/-- Even the existential witness uses the original iterated quotient groups. -/
example : @ExistsCanonical R S X Y Z r₀ s₀ gx₀ gy₀ gz₀ xR₀ yR₀ yS₀ zS₀ hY =
    (letI := GL
     letI := GT
     ∃ E : L ≃+ T, @Canonical R S X Y Z r₀ s₀ gx₀ gy₀ gz₀ xR₀ yR₀ yS₀ zS₀ hY E) := rfl

/-- Both complete outer lifts preserve the named group structures. -/
example (E : letI := GL; letI := GT; L ≃+ T) :
    @NestedLiftFormulas R S X Y Z r₀ s₀ gx₀ gy₀ gz₀ xR₀ yR₀ yS₀ zS₀ hY E =
      (E.toAddMonoidHom =
        @lift S Q Z s₀ GQ gz₀ AQ zS₀ T GT
          (@forwardPairing R S X Y Z r₀ s₀ gx₀ gy₀ gz₀ xR₀ yR₀ yS₀ zS₀ hY) (@forwardPairing_balanced R S X Y Z r₀ s₀ gx₀ gy₀ gz₀ xR₀ yR₀ yS₀ zS₀ hY) ∧
       E.symm.toAddMonoidHom =
        @lift R X V r₀ gx₀ GV xR₀ AV L GL
          (@inversePairing R S X Y Z r₀ s₀ gx₀ gy₀ gz₀ xR₀ yR₀ yS₀ zS₀ hY) (@inversePairing_balanced R S X Y Z r₀ s₀ gx₀ gy₀ gz₀ xR₀ yR₀ yS₀ zS₀ hY)) := rfl

/-- All six original carriers and both one-sided maps survive competitors. -/
example : @Naturality R S X Y Z X' Y' Z' r₀ s₀ gx₀ gy₀ gz₀ gx'₀ gy'₀ gz'₀ xR₀ yR₀ yS₀ zS₀ xR'₀ yR'₀ yS'₀ zS'₀ hY hY' =
    (letI := r₀
     letI := s₀
     letI := gx₀
     letI := gy₀
     letI := gz₀
     letI := gx'₀
     letI := gy'₀
     letI := gz'₀
     letI := xR₀
     letI := yR₀
     letI := yS₀
     letI := zS₀
     letI := xR'₀
     letI := yR'₀
     letI := yS'₀
     letI := zS'₀
     letI := GQ
     letI := GV
     letI := GQ'
     letI := GV'
     letI := AQ
     letI := AV
     letI := AQ'
     letI := AV'
     letI := GL
     letI := GT
     letI := GL'
     letI := GT'
     ∀ (E : L ≃+ T) (E' : L' ≃+ T'),
       Canonical R S X Y Z hY E → Canonical R S X' Y' Z' hY' E' →
       ∀ (f : NonUnitalModuleHom Rᵐᵒᵖ X X')
         (g : NonUnitalBimoduleHom R S Y Y') (k : NonUnitalModuleHom S Z Z'),
         let ML := NonUnitalModuleTensor.map S (NonUnitalBimoduleTensor.rightMap hY hY' f g) k
         let MR := NonUnitalModuleTensor.map R f (NonUnitalBimoduleTensor.leftMap hY hY' g k)
         E'.toAddMonoidHom.comp ML = MR.comp E.toAddMonoidHom ∧
           E'.symm.toAddMonoidHom.comp MR = ML.comp E.symm.toAddMonoidHom) := rfl

end CompetingStructures

/-! Subsingleton carriers remain in scope at independent universes. -/

section SubsingletonCarriers
universe uA uM
local instance (A : Type uA) [NonUnitalRing A]
    (M : Type uM) [AddCommGroup M] [Subsingleton M] : NonUnitalModule A M :=
  NonUnitalModule.zero

variable (R : Type uR) (S : Type uS) [NonUnitalRing R] [NonUnitalRing S]

example : Prop := ExistsCanonical R S PUnit.{uX + 1} PUnit.{uY + 1} PUnit.{uZ + 1}
  actionsCommute_of_subsingleton

example : Prop := Naturality R S
  PUnit.{uX + 1} PUnit.{uY + 1} PUnit.{uZ + 1}
  PUnit.{uX' + 1} PUnit.{uY' + 1} PUnit.{uZ' + 1}
  actionsCommute_of_subsingleton actionsCommute_of_subsingleton

end SubsingletonCarriers

private def integerPairing : ℤ →+ ℤ →+ ℤ where
  toFun x :=
    { toFun y := x * y
      map_zero' := mul_zero x
      map_add' := mul_add x }
  map_zero' := AddMonoidHom.ext zero_mul
  map_add' x x' := AddMonoidHom.ext (fun y => add_mul x x' y)

/-! Zero actions over the unital ring ℤ retain nonzero actual iterated quotients. -/

section ZeroIntegerActions
local instance : NonUnitalModule ℤ ℤ := NonUnitalModule.zero
local instance : NonUnitalModule ℤᵐᵒᵖ ℤ := NonUnitalModule.zero

private theorem zeroCommute : ActionsCommute ℤ ℤ ℤ :=
  actionsCommute_zero_left

local instance : NonUnitalModule ℤᵐᵒᵖ (Tensor ℤ ℤ ℤ) := rightModule ℤ zeroCommute
local instance : NonUnitalModule ℤ (Tensor ℤ ℤ ℤ) := leftModule zeroCommute ℤ

example : Prop := ExistsCanonical ℤ ℤ ℤ ℤ ℤ zeroCommute
example : Prop := Naturality ℤ ℤ ℤ ℤ ℤ ℤ ℤ ℤ zeroCommute zeroCommute

example : ¬ IsNondegenerate ℤ ℤ := not_isNondegenerate_zero
example : ¬ IsRightNondegenerate ℤ ℤ := not_isNondegenerate_zero
example : ¬ ∀ x : ℤ, (1 : ℤ) • x = x := by
  intro h
  have h' := h 1
  change (0 : ℤ) = 1 at h'
  exact zero_ne_one h'

private theorem zeroIntegerPairing_balanced : IsBalanced ℤ integerPairing := by
  intro a x y
  change (0 : ℤ) * y = x * 0
  rw [zero_mul, mul_zero]

private def integerEvaluation : Tensor ℤ ℤ ℤ →+ ℤ :=
  lift ℤ integerPairing zeroIntegerPairing_balanced

private theorem zeroRightScalar (s : ℤᵐᵒᵖ) :
    NonUnitalModule.toEndHom (rightModule ℤ zeroCommute) s = 0 := by
  apply NonUnitalModuleTensor.hom_ext ℤ
  intro x y
  change tmul ℤ ℤ ℤ x 0 = 0
  exact NonUnitalModuleTensor.tmul_zero ℤ ℤ ℤ x

private theorem zeroLeftScalar (r : ℤ) :
    NonUnitalModule.toEndHom (leftModule zeroCommute ℤ) r = 0 := by
  apply NonUnitalModuleTensor.hom_ext ℤ
  intro y z
  change tmul ℤ ℤ ℤ 0 z = 0
  exact NonUnitalModuleTensor.zero_tmul ℤ ℤ ℤ z

private def leftEvaluationPairing : Tensor ℤ ℤ ℤ →+ ℤ →+ ℤ :=
  integerPairing.comp integerEvaluation

private theorem leftEvaluationPairing_balanced : IsBalanced ℤ leftEvaluationPairing := by
  intro s t z
  change integerEvaluation (op s • t) * z = integerEvaluation t * 0
  have h : op s • t = 0 := DFunLike.congr_fun (zeroRightScalar (op s)) t
  rw [h, map_zero, zero_mul, mul_zero]

private def rightEvaluationPairing : ℤ →+ Tensor ℤ ℤ ℤ →+ ℤ where
  toFun x := (integerPairing x).comp integerEvaluation
  map_zero' := by ext u; exact zero_mul _
  map_add' x x' := by ext u; exact add_mul x x' _

private theorem rightEvaluationPairing_balanced : IsBalanced ℤ rightEvaluationPairing := by
  intro r x u
  change 0 * integerEvaluation u = x * integerEvaluation (r • u)
  have h : r • u = 0 := DFunLike.congr_fun (zeroLeftScalar r) u
  rw [h, map_zero, zero_mul, mul_zero]

/-- A direct integer-valued lift detects a nonzero left iterated pure tensor. -/
private theorem leftZeroActions_nonzero :
    tmul ℤ (Tensor ℤ ℤ ℤ) ℤ (tmul ℤ ℤ ℤ 1 1) 1 ≠ 0 := by
  intro h
  have h' := congrArg (lift ℤ leftEvaluationPairing leftEvaluationPairing_balanced) h
  change (1 : ℤ) = 0 at h'
  exact one_ne_zero h'

/-- The right iterated quotient is likewise nonzero, without using an associator. -/
private theorem rightZeroActions_nonzero :
    tmul ℤ ℤ (Tensor ℤ ℤ ℤ) 1 (tmul ℤ ℤ ℤ 1 1) ≠ 0 := by
  intro h
  have h' := congrArg (lift ℤ rightEvaluationPairing rightEvaluationPairing_balanced) h
  change (1 : ℤ) = 0 at h'
  exact one_ne_zero h'

example : Nontrivial (LeftTensor ℤ ℤ ℤ ℤ ℤ zeroCommute) :=
  ⟨⟨tmul ℤ (Tensor ℤ ℤ ℤ) ℤ (tmul ℤ ℤ ℤ 1 1) 1, 0, leftZeroActions_nonzero⟩⟩

example : Nontrivial (RightTensor ℤ ℤ ℤ ℤ ℤ zeroCommute) :=
  ⟨⟨tmul ℤ ℤ (Tensor ℤ ℤ ℤ) 1 (tmul ℤ ℤ ℤ 1 1), 0, rightZeroActions_nonzero⟩⟩

example (x y z : ℤ) :
    forwardPairing ℤ ℤ ℤ ℤ ℤ zeroCommute (tmul ℤ ℤ ℤ x y) z =
      tmul ℤ ℤ (Tensor ℤ ℤ ℤ) x (tmul ℤ ℤ ℤ y z) := rfl

example (x y z : ℤ) :
    inversePairing ℤ ℤ ℤ ℤ ℤ zeroCommute x (tmul ℤ ℤ ℤ y z) =
      tmul ℤ (Tensor ℤ ℤ ℤ) ℤ (tmul ℤ ℤ ℤ x y) z := rfl

end ZeroIntegerActions

/-! The regular integer actions are admitted with their actual multiplication. -/

section RegularIntegerActions
local instance : NonUnitalModule ℤ ℤ := (NonUnitalBimoduleCat.regular ℤ).isLeftModule
local instance : NonUnitalModule ℤᵐᵒᵖ ℤ := (NonUnitalBimoduleCat.regular ℤ).isRightModule

private theorem regularCommute : ActionsCommute ℤ ℤ ℤ :=
  (NonUnitalBimoduleCat.regular ℤ).actionsCommute

local instance : NonUnitalModule ℤᵐᵒᵖ (Tensor ℤ ℤ ℤ) := rightModule ℤ regularCommute
local instance : NonUnitalModule ℤ (Tensor ℤ ℤ ℤ) := leftModule regularCommute ℤ

example : Prop := ExistsCanonical ℤ ℤ ℤ ℤ ℤ regularCommute
example : Prop := Naturality ℤ ℤ ℤ ℤ ℤ ℤ ℤ ℤ regularCommute regularCommute

example : op (2 : ℤ) • tmul ℤ ℤ ℤ 1 1 = tmul ℤ ℤ ℤ 1 2 := rfl
example : (2 : ℤ) • tmul ℤ ℤ ℤ 1 1 = tmul ℤ ℤ ℤ 2 1 := rfl

example (x y z : ℤ) :
    forwardPairing ℤ ℤ ℤ ℤ ℤ regularCommute (tmul ℤ ℤ ℤ x y) z =
      tmul ℤ ℤ (Tensor ℤ ℤ ℤ) x (tmul ℤ ℤ ℤ y z) := rfl

example (x y z : ℤ) :
    inversePairing ℤ ℤ ℤ ℤ ℤ regularCommute x (tmul ℤ ℤ ℤ y z) =
      tmul ℤ (Tensor ℤ ℤ ℤ) ℤ (tmul ℤ ℤ ℤ x y) z := rfl

end RegularIntegerActions

end Langlands.Algebra.NonUnitalTensorAssociativityChecks
