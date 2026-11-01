import Langlands.Algebra.NonUnitalTensorHomAdjunctionStatements

/-!
# Interface and scope checks for the original-action tensor-Hom targets

Internal checks of complete unapplied types, exact unfoldings, independent
universes, competing structures and zero, subsingleton and regular actions.
These do not prove the principal tensor-Hom propositions.
-/

set_option autoImplicit false

namespace Langlands.Algebra.NonUnitalTensorHomAdjunctionChecks

open MulOpposite
open NonUnitalTensorHomAdjunction
open NonUnitalModuleTensor (Tensor tmul lift)
open NonUnitalBimoduleTensor (rightModule leftModule rightMap leftMap)
open NonUnitalBimoduleHomActions
  (rightSourceAction sourceAction rightSourceMap sourceMap mapAddHom postcomposeAddHom)

universe uR uS uX uY uZ uX' uY' uZ'

section Interfaces
set_option linter.unusedVariables false

example : ∀ {A : Type uX} {B : Type uY} [AddCommGroup A] [AddCommGroup B],
    (A ≃+ B) → Prop := @InverseIdentities

/-! Full unapplied signatures at Arbitrary universes. -/

example : ∀ (R : Type uR) (S : Type uS) (X : Type uX) (Y : Type uY) (Z : Type uZ)
    [NonUnitalRing R] [NonUnitalRing S]
    [AddCommGroup X] [AddCommGroup Y] [AddCommGroup Z]
    [NonUnitalModule Rᵐᵒᵖ X] [NonUnitalModule R Y]
    [NonUnitalModule Sᵐᵒᵖ Y] [NonUnitalModule Sᵐᵒᵖ Z]
    (hY : ActionsCommute R S Y)
    (E : (Right.TensorHom R S X Y Z hY ≃+ Right.CurriedHom R S X Y Z hY)), Prop := @Right.Canonical

example : ∀ (R : Type uR) (S : Type uS) (X : Type uX) (Y : Type uY) (Z : Type uZ)
    [NonUnitalRing R] [NonUnitalRing S]
    [AddCommGroup X] [AddCommGroup Y] [AddCommGroup Z]
    [NonUnitalModule Rᵐᵒᵖ X] [NonUnitalModule R Y]
    [NonUnitalModule Sᵐᵒᵖ Y] [NonUnitalModule Sᵐᵒᵖ Z]
    (hY : ActionsCommute R S Y), Prop := @Right.ExistsCanonical

example : ∀ (R : Type uR) (S : Type uS) (X : Type uX) (Y : Type uY) (Z : Type uZ)
    [NonUnitalRing R] [NonUnitalRing S]
    [AddCommGroup X] [AddCommGroup Y] [AddCommGroup Z]
    [NonUnitalModule Rᵐᵒᵖ X] [NonUnitalModule R Y]
    [NonUnitalModule Sᵐᵒᵖ Y] [NonUnitalModule Sᵐᵒᵖ Z]
    (hY : ActionsCommute R S Y)
    (hR : IsIdempotented R) (E : (Right.TensorHom R S X Y Z hY ≃+ Right.CurriedHom R S X Y Z hY)) (End : (Right.TensorHom R S X Y Z hY ≃+ Right.RefinedHom R S X Y Z hY hR)), Prop := @Right.RefinedCanonical

example : ∀ (R : Type uR) (S : Type uS) (X : Type uX) (Y : Type uY) (Z : Type uZ)
    [NonUnitalRing R] [NonUnitalRing S]
    [AddCommGroup X] [AddCommGroup Y] [AddCommGroup Z]
    [NonUnitalModule Rᵐᵒᵖ X] [NonUnitalModule R Y]
    [NonUnitalModule Sᵐᵒᵖ Y] [NonUnitalModule Sᵐᵒᵖ Z]
    (hY : ActionsCommute R S Y)
    (hR : IsIdempotented R), Prop := @Right.ExistsRefinedCanonical

example : ∀ (R : Type uR) (S : Type uS) (X : Type uX) (Y : Type uY) (Z : Type uZ)
    [NonUnitalRing R] [NonUnitalRing S]
    [AddCommGroup X] [AddCommGroup Y] [AddCommGroup Z]
    [NonUnitalModule Rᵐᵒᵖ X] [NonUnitalModule R Y]
    [NonUnitalModule Sᵐᵒᵖ Y] [NonUnitalModule Sᵐᵒᵖ Z]
    (hY : ActionsCommute R S Y)
    {X' : Type uX'} {Y' : Type uY'} {Z' : Type uZ'}
    [AddCommGroup X'] [AddCommGroup Y'] [AddCommGroup Z']
    [NonUnitalModule Rᵐᵒᵖ X'] [NonUnitalModule R Y']
    [NonUnitalModule Sᵐᵒᵖ Y'] [NonUnitalModule Sᵐᵒᵖ Z']
    (hY' : ActionsCommute R S Y')
    (f : NonUnitalModuleHom Rᵐᵒᵖ X' X) (g : NonUnitalBimoduleHom R S Y' Y)
    (k : NonUnitalModuleHom Sᵐᵒᵖ Z Z')
    (E : (Right.TensorHom R S X Y Z hY ≃+ Right.CurriedHom R S X Y Z hY)) (E' : (Right.TensorHom R S X' Y' Z' hY' ≃+ Right.CurriedHom R S X' Y' Z' hY')), Prop := @Right.Naturality

example : ∀ (R : Type uR) (S : Type uS) (X : Type uX) (Y : Type uY) (Z : Type uZ)
    [NonUnitalRing R] [NonUnitalRing S]
    [AddCommGroup X] [AddCommGroup Y] [AddCommGroup Z]
    [NonUnitalModule Rᵐᵒᵖ X] [NonUnitalModule R Y]
    [NonUnitalModule Sᵐᵒᵖ Y] [NonUnitalModule Sᵐᵒᵖ Z]
    (hY : ActionsCommute R S Y)
    {X' : Type uX'} {Y' : Type uY'} {Z' : Type uZ'}
    [AddCommGroup X'] [AddCommGroup Y'] [AddCommGroup Z']
    [NonUnitalModule Rᵐᵒᵖ X'] [NonUnitalModule R Y']
    [NonUnitalModule Sᵐᵒᵖ Y'] [NonUnitalModule Sᵐᵒᵖ Z']
    (hY' : ActionsCommute R S Y')
    (f : NonUnitalModuleHom Rᵐᵒᵖ X' X) (g : NonUnitalBimoduleHom R S Y' Y)
    (k : NonUnitalModuleHom Sᵐᵒᵖ Z Z')
    (hR : IsIdempotented R) (End : (Right.TensorHom R S X Y Z hY ≃+ Right.RefinedHom R S X Y Z hY hR)) (End' : (Right.TensorHom R S X' Y' Z' hY' ≃+ Right.RefinedHom R S X' Y' Z' hY' hR)), Prop := @Right.RefinedNaturality

example : ∀ (R : Type uR) (S : Type uS) (X : Type uX) (Y : Type uY) (Z : Type uZ)
    [NonUnitalRing R] [NonUnitalRing S]
    [AddCommGroup X] [AddCommGroup Y] [AddCommGroup Z]
    [NonUnitalModule R X] [NonUnitalModule S Y]
    [NonUnitalModule Rᵐᵒᵖ Y] [NonUnitalModule S Z]
    (hY : ActionsCommute S R Y)
    (E : (Left.TensorHom R S X Y Z hY ≃+ Left.CurriedHom R S X Y Z hY)), Prop := @Left.Canonical

example : ∀ (R : Type uR) (S : Type uS) (X : Type uX) (Y : Type uY) (Z : Type uZ)
    [NonUnitalRing R] [NonUnitalRing S]
    [AddCommGroup X] [AddCommGroup Y] [AddCommGroup Z]
    [NonUnitalModule R X] [NonUnitalModule S Y]
    [NonUnitalModule Rᵐᵒᵖ Y] [NonUnitalModule S Z]
    (hY : ActionsCommute S R Y), Prop := @Left.ExistsCanonical

example : ∀ (R : Type uR) (S : Type uS) (X : Type uX) (Y : Type uY) (Z : Type uZ)
    [NonUnitalRing R] [NonUnitalRing S]
    [AddCommGroup X] [AddCommGroup Y] [AddCommGroup Z]
    [NonUnitalModule R X] [NonUnitalModule S Y]
    [NonUnitalModule Rᵐᵒᵖ Y] [NonUnitalModule S Z]
    (hY : ActionsCommute S R Y)
    (hR : IsIdempotented R) (E : (Left.TensorHom R S X Y Z hY ≃+ Left.CurriedHom R S X Y Z hY)) (End : (Left.TensorHom R S X Y Z hY ≃+ Left.RefinedHom R S X Y Z hY hR)), Prop := @Left.RefinedCanonical

example : ∀ (R : Type uR) (S : Type uS) (X : Type uX) (Y : Type uY) (Z : Type uZ)
    [NonUnitalRing R] [NonUnitalRing S]
    [AddCommGroup X] [AddCommGroup Y] [AddCommGroup Z]
    [NonUnitalModule R X] [NonUnitalModule S Y]
    [NonUnitalModule Rᵐᵒᵖ Y] [NonUnitalModule S Z]
    (hY : ActionsCommute S R Y)
    (hR : IsIdempotented R), Prop := @Left.ExistsRefinedCanonical

example : ∀ (R : Type uR) (S : Type uS) (X : Type uX) (Y : Type uY) (Z : Type uZ)
    [NonUnitalRing R] [NonUnitalRing S]
    [AddCommGroup X] [AddCommGroup Y] [AddCommGroup Z]
    [NonUnitalModule R X] [NonUnitalModule S Y]
    [NonUnitalModule Rᵐᵒᵖ Y] [NonUnitalModule S Z]
    (hY : ActionsCommute S R Y)
    {X' : Type uX'} {Y' : Type uY'} {Z' : Type uZ'}
    [AddCommGroup X'] [AddCommGroup Y'] [AddCommGroup Z']
    [NonUnitalModule R X'] [NonUnitalModule S Y']
    [NonUnitalModule Rᵐᵒᵖ Y'] [NonUnitalModule S Z']
    (hY' : ActionsCommute S R Y')
    (f : NonUnitalModuleHom R X' X) (g : NonUnitalBimoduleHom S R Y' Y)
    (k : NonUnitalModuleHom S Z Z')
    (E : (Left.TensorHom R S X Y Z hY ≃+ Left.CurriedHom R S X Y Z hY)) (E' : (Left.TensorHom R S X' Y' Z' hY' ≃+ Left.CurriedHom R S X' Y' Z' hY')), Prop := @Left.Naturality

example : ∀ (R : Type uR) (S : Type uS) (X : Type uX) (Y : Type uY) (Z : Type uZ)
    [NonUnitalRing R] [NonUnitalRing S]
    [AddCommGroup X] [AddCommGroup Y] [AddCommGroup Z]
    [NonUnitalModule R X] [NonUnitalModule S Y]
    [NonUnitalModule Rᵐᵒᵖ Y] [NonUnitalModule S Z]
    (hY : ActionsCommute S R Y)
    {X' : Type uX'} {Y' : Type uY'} {Z' : Type uZ'}
    [AddCommGroup X'] [AddCommGroup Y'] [AddCommGroup Z']
    [NonUnitalModule R X'] [NonUnitalModule S Y']
    [NonUnitalModule Rᵐᵒᵖ Y'] [NonUnitalModule S Z']
    (hY' : ActionsCommute S R Y')
    (f : NonUnitalModuleHom R X' X) (g : NonUnitalBimoduleHom S R Y' Y)
    (k : NonUnitalModuleHom S Z Z')
    (hR : IsIdempotented R) (End : (Left.TensorHom R S X Y Z hY ≃+ Left.RefinedHom R S X Y Z hY hR)) (End' : (Left.TensorHom R S X' Y' Z' hY' ≃+ Left.RefinedHom R S X' Y' Z' hY' hR)), Prop := @Left.RefinedNaturality

example : Prop := Right.ExistenceTheorem.{uR, uS, uX, uY, uZ}

example : Prop := Right.RefinedExistenceTheorem.{uR, uS, uX, uY, uZ}

example : Prop := Right.NaturalityTheorem.{uR, uS, uX, uY, uZ, uX', uY', uZ'}

example : Prop := Right.RefinedNaturalityTheorem.{uR, uS, uX, uY, uZ, uX', uY', uZ'}

example : Prop := Left.ExistenceTheorem.{uR, uS, uX, uY, uZ}

example : Prop := Left.RefinedExistenceTheorem.{uR, uS, uX, uY, uZ}

example : Prop := Left.NaturalityTheorem.{uR, uS, uX, uY, uZ, uX', uY', uZ'}

example : Prop := Left.RefinedNaturalityTheorem.{uR, uS, uX, uY, uZ, uX', uY', uZ'}

example : Prop := NonUnitalTensorHomAdjunctionTheorem.{uR, uS, uX, uY, uZ, uX', uY', uZ'}

/-! Full unapplied signatures at SmallLarge universes. -/

example : ∀ (R : Type 0) (S : Type 1) (X : Type 0) (Y : Type 1) (Z : Type 0)
    [NonUnitalRing R] [NonUnitalRing S]
    [AddCommGroup X] [AddCommGroup Y] [AddCommGroup Z]
    [NonUnitalModule Rᵐᵒᵖ X] [NonUnitalModule R Y]
    [NonUnitalModule Sᵐᵒᵖ Y] [NonUnitalModule Sᵐᵒᵖ Z]
    (hY : ActionsCommute R S Y)
    (E : (Right.TensorHom R S X Y Z hY ≃+ Right.CurriedHom R S X Y Z hY)), Prop := @Right.Canonical

example : ∀ (R : Type 0) (S : Type 1) (X : Type 0) (Y : Type 1) (Z : Type 0)
    [NonUnitalRing R] [NonUnitalRing S]
    [AddCommGroup X] [AddCommGroup Y] [AddCommGroup Z]
    [NonUnitalModule Rᵐᵒᵖ X] [NonUnitalModule R Y]
    [NonUnitalModule Sᵐᵒᵖ Y] [NonUnitalModule Sᵐᵒᵖ Z]
    (hY : ActionsCommute R S Y), Prop := @Right.ExistsCanonical

example : ∀ (R : Type 0) (S : Type 1) (X : Type 0) (Y : Type 1) (Z : Type 0)
    [NonUnitalRing R] [NonUnitalRing S]
    [AddCommGroup X] [AddCommGroup Y] [AddCommGroup Z]
    [NonUnitalModule Rᵐᵒᵖ X] [NonUnitalModule R Y]
    [NonUnitalModule Sᵐᵒᵖ Y] [NonUnitalModule Sᵐᵒᵖ Z]
    (hY : ActionsCommute R S Y)
    (hR : IsIdempotented R) (E : (Right.TensorHom R S X Y Z hY ≃+ Right.CurriedHom R S X Y Z hY)) (End : (Right.TensorHom R S X Y Z hY ≃+ Right.RefinedHom R S X Y Z hY hR)), Prop := @Right.RefinedCanonical

example : ∀ (R : Type 0) (S : Type 1) (X : Type 0) (Y : Type 1) (Z : Type 0)
    [NonUnitalRing R] [NonUnitalRing S]
    [AddCommGroup X] [AddCommGroup Y] [AddCommGroup Z]
    [NonUnitalModule Rᵐᵒᵖ X] [NonUnitalModule R Y]
    [NonUnitalModule Sᵐᵒᵖ Y] [NonUnitalModule Sᵐᵒᵖ Z]
    (hY : ActionsCommute R S Y)
    (hR : IsIdempotented R), Prop := @Right.ExistsRefinedCanonical

example : ∀ (R : Type 0) (S : Type 1) (X : Type 0) (Y : Type 1) (Z : Type 0)
    [NonUnitalRing R] [NonUnitalRing S]
    [AddCommGroup X] [AddCommGroup Y] [AddCommGroup Z]
    [NonUnitalModule Rᵐᵒᵖ X] [NonUnitalModule R Y]
    [NonUnitalModule Sᵐᵒᵖ Y] [NonUnitalModule Sᵐᵒᵖ Z]
    (hY : ActionsCommute R S Y)
    {X' : Type 1} {Y' : Type 0} {Z' : Type 1}
    [AddCommGroup X'] [AddCommGroup Y'] [AddCommGroup Z']
    [NonUnitalModule Rᵐᵒᵖ X'] [NonUnitalModule R Y']
    [NonUnitalModule Sᵐᵒᵖ Y'] [NonUnitalModule Sᵐᵒᵖ Z']
    (hY' : ActionsCommute R S Y')
    (f : NonUnitalModuleHom Rᵐᵒᵖ X' X) (g : NonUnitalBimoduleHom R S Y' Y)
    (k : NonUnitalModuleHom Sᵐᵒᵖ Z Z')
    (E : (Right.TensorHom R S X Y Z hY ≃+ Right.CurriedHom R S X Y Z hY)) (E' : (Right.TensorHom R S X' Y' Z' hY' ≃+ Right.CurriedHom R S X' Y' Z' hY')), Prop := @Right.Naturality

example : ∀ (R : Type 0) (S : Type 1) (X : Type 0) (Y : Type 1) (Z : Type 0)
    [NonUnitalRing R] [NonUnitalRing S]
    [AddCommGroup X] [AddCommGroup Y] [AddCommGroup Z]
    [NonUnitalModule Rᵐᵒᵖ X] [NonUnitalModule R Y]
    [NonUnitalModule Sᵐᵒᵖ Y] [NonUnitalModule Sᵐᵒᵖ Z]
    (hY : ActionsCommute R S Y)
    {X' : Type 1} {Y' : Type 0} {Z' : Type 1}
    [AddCommGroup X'] [AddCommGroup Y'] [AddCommGroup Z']
    [NonUnitalModule Rᵐᵒᵖ X'] [NonUnitalModule R Y']
    [NonUnitalModule Sᵐᵒᵖ Y'] [NonUnitalModule Sᵐᵒᵖ Z']
    (hY' : ActionsCommute R S Y')
    (f : NonUnitalModuleHom Rᵐᵒᵖ X' X) (g : NonUnitalBimoduleHom R S Y' Y)
    (k : NonUnitalModuleHom Sᵐᵒᵖ Z Z')
    (hR : IsIdempotented R) (End : (Right.TensorHom R S X Y Z hY ≃+ Right.RefinedHom R S X Y Z hY hR)) (End' : (Right.TensorHom R S X' Y' Z' hY' ≃+ Right.RefinedHom R S X' Y' Z' hY' hR)), Prop := @Right.RefinedNaturality

example : ∀ (R : Type 0) (S : Type 1) (X : Type 0) (Y : Type 1) (Z : Type 0)
    [NonUnitalRing R] [NonUnitalRing S]
    [AddCommGroup X] [AddCommGroup Y] [AddCommGroup Z]
    [NonUnitalModule R X] [NonUnitalModule S Y]
    [NonUnitalModule Rᵐᵒᵖ Y] [NonUnitalModule S Z]
    (hY : ActionsCommute S R Y)
    (E : (Left.TensorHom R S X Y Z hY ≃+ Left.CurriedHom R S X Y Z hY)), Prop := @Left.Canonical

example : ∀ (R : Type 0) (S : Type 1) (X : Type 0) (Y : Type 1) (Z : Type 0)
    [NonUnitalRing R] [NonUnitalRing S]
    [AddCommGroup X] [AddCommGroup Y] [AddCommGroup Z]
    [NonUnitalModule R X] [NonUnitalModule S Y]
    [NonUnitalModule Rᵐᵒᵖ Y] [NonUnitalModule S Z]
    (hY : ActionsCommute S R Y), Prop := @Left.ExistsCanonical

example : ∀ (R : Type 0) (S : Type 1) (X : Type 0) (Y : Type 1) (Z : Type 0)
    [NonUnitalRing R] [NonUnitalRing S]
    [AddCommGroup X] [AddCommGroup Y] [AddCommGroup Z]
    [NonUnitalModule R X] [NonUnitalModule S Y]
    [NonUnitalModule Rᵐᵒᵖ Y] [NonUnitalModule S Z]
    (hY : ActionsCommute S R Y)
    (hR : IsIdempotented R) (E : (Left.TensorHom R S X Y Z hY ≃+ Left.CurriedHom R S X Y Z hY)) (End : (Left.TensorHom R S X Y Z hY ≃+ Left.RefinedHom R S X Y Z hY hR)), Prop := @Left.RefinedCanonical

example : ∀ (R : Type 0) (S : Type 1) (X : Type 0) (Y : Type 1) (Z : Type 0)
    [NonUnitalRing R] [NonUnitalRing S]
    [AddCommGroup X] [AddCommGroup Y] [AddCommGroup Z]
    [NonUnitalModule R X] [NonUnitalModule S Y]
    [NonUnitalModule Rᵐᵒᵖ Y] [NonUnitalModule S Z]
    (hY : ActionsCommute S R Y)
    (hR : IsIdempotented R), Prop := @Left.ExistsRefinedCanonical

example : ∀ (R : Type 0) (S : Type 1) (X : Type 0) (Y : Type 1) (Z : Type 0)
    [NonUnitalRing R] [NonUnitalRing S]
    [AddCommGroup X] [AddCommGroup Y] [AddCommGroup Z]
    [NonUnitalModule R X] [NonUnitalModule S Y]
    [NonUnitalModule Rᵐᵒᵖ Y] [NonUnitalModule S Z]
    (hY : ActionsCommute S R Y)
    {X' : Type 1} {Y' : Type 0} {Z' : Type 1}
    [AddCommGroup X'] [AddCommGroup Y'] [AddCommGroup Z']
    [NonUnitalModule R X'] [NonUnitalModule S Y']
    [NonUnitalModule Rᵐᵒᵖ Y'] [NonUnitalModule S Z']
    (hY' : ActionsCommute S R Y')
    (f : NonUnitalModuleHom R X' X) (g : NonUnitalBimoduleHom S R Y' Y)
    (k : NonUnitalModuleHom S Z Z')
    (E : (Left.TensorHom R S X Y Z hY ≃+ Left.CurriedHom R S X Y Z hY)) (E' : (Left.TensorHom R S X' Y' Z' hY' ≃+ Left.CurriedHom R S X' Y' Z' hY')), Prop := @Left.Naturality

example : ∀ (R : Type 0) (S : Type 1) (X : Type 0) (Y : Type 1) (Z : Type 0)
    [NonUnitalRing R] [NonUnitalRing S]
    [AddCommGroup X] [AddCommGroup Y] [AddCommGroup Z]
    [NonUnitalModule R X] [NonUnitalModule S Y]
    [NonUnitalModule Rᵐᵒᵖ Y] [NonUnitalModule S Z]
    (hY : ActionsCommute S R Y)
    {X' : Type 1} {Y' : Type 0} {Z' : Type 1}
    [AddCommGroup X'] [AddCommGroup Y'] [AddCommGroup Z']
    [NonUnitalModule R X'] [NonUnitalModule S Y']
    [NonUnitalModule Rᵐᵒᵖ Y'] [NonUnitalModule S Z']
    (hY' : ActionsCommute S R Y')
    (f : NonUnitalModuleHom R X' X) (g : NonUnitalBimoduleHom S R Y' Y)
    (k : NonUnitalModuleHom S Z Z')
    (hR : IsIdempotented R) (End : (Left.TensorHom R S X Y Z hY ≃+ Left.RefinedHom R S X Y Z hY hR)) (End' : (Left.TensorHom R S X' Y' Z' hY' ≃+ Left.RefinedHom R S X' Y' Z' hY' hR)), Prop := @Left.RefinedNaturality

example : Prop := Right.ExistenceTheorem.{0, 1, 0, 1, 0}

example : Prop := Right.RefinedExistenceTheorem.{0, 1, 0, 1, 0}

example : Prop := Right.NaturalityTheorem.{0, 1, 0, 1, 0, 1, 0, 1}

example : Prop := Right.RefinedNaturalityTheorem.{0, 1, 0, 1, 0, 1, 0, 1}

example : Prop := Left.ExistenceTheorem.{0, 1, 0, 1, 0}

example : Prop := Left.RefinedExistenceTheorem.{0, 1, 0, 1, 0}

example : Prop := Left.NaturalityTheorem.{0, 1, 0, 1, 0, 1, 0, 1}

example : Prop := Left.RefinedNaturalityTheorem.{0, 1, 0, 1, 0, 1, 0, 1}

example : Prop := NonUnitalTensorHomAdjunctionTheorem.{0, 1, 0, 1, 0, 1, 0, 1}

/-! Full unapplied signatures at LargeSmall universes. -/

example : ∀ (R : Type 1) (S : Type 0) (X : Type 1) (Y : Type 0) (Z : Type 1)
    [NonUnitalRing R] [NonUnitalRing S]
    [AddCommGroup X] [AddCommGroup Y] [AddCommGroup Z]
    [NonUnitalModule Rᵐᵒᵖ X] [NonUnitalModule R Y]
    [NonUnitalModule Sᵐᵒᵖ Y] [NonUnitalModule Sᵐᵒᵖ Z]
    (hY : ActionsCommute R S Y)
    (E : (Right.TensorHom R S X Y Z hY ≃+ Right.CurriedHom R S X Y Z hY)), Prop := @Right.Canonical

example : ∀ (R : Type 1) (S : Type 0) (X : Type 1) (Y : Type 0) (Z : Type 1)
    [NonUnitalRing R] [NonUnitalRing S]
    [AddCommGroup X] [AddCommGroup Y] [AddCommGroup Z]
    [NonUnitalModule Rᵐᵒᵖ X] [NonUnitalModule R Y]
    [NonUnitalModule Sᵐᵒᵖ Y] [NonUnitalModule Sᵐᵒᵖ Z]
    (hY : ActionsCommute R S Y), Prop := @Right.ExistsCanonical

example : ∀ (R : Type 1) (S : Type 0) (X : Type 1) (Y : Type 0) (Z : Type 1)
    [NonUnitalRing R] [NonUnitalRing S]
    [AddCommGroup X] [AddCommGroup Y] [AddCommGroup Z]
    [NonUnitalModule Rᵐᵒᵖ X] [NonUnitalModule R Y]
    [NonUnitalModule Sᵐᵒᵖ Y] [NonUnitalModule Sᵐᵒᵖ Z]
    (hY : ActionsCommute R S Y)
    (hR : IsIdempotented R) (E : (Right.TensorHom R S X Y Z hY ≃+ Right.CurriedHom R S X Y Z hY)) (End : (Right.TensorHom R S X Y Z hY ≃+ Right.RefinedHom R S X Y Z hY hR)), Prop := @Right.RefinedCanonical

example : ∀ (R : Type 1) (S : Type 0) (X : Type 1) (Y : Type 0) (Z : Type 1)
    [NonUnitalRing R] [NonUnitalRing S]
    [AddCommGroup X] [AddCommGroup Y] [AddCommGroup Z]
    [NonUnitalModule Rᵐᵒᵖ X] [NonUnitalModule R Y]
    [NonUnitalModule Sᵐᵒᵖ Y] [NonUnitalModule Sᵐᵒᵖ Z]
    (hY : ActionsCommute R S Y)
    (hR : IsIdempotented R), Prop := @Right.ExistsRefinedCanonical

example : ∀ (R : Type 1) (S : Type 0) (X : Type 1) (Y : Type 0) (Z : Type 1)
    [NonUnitalRing R] [NonUnitalRing S]
    [AddCommGroup X] [AddCommGroup Y] [AddCommGroup Z]
    [NonUnitalModule Rᵐᵒᵖ X] [NonUnitalModule R Y]
    [NonUnitalModule Sᵐᵒᵖ Y] [NonUnitalModule Sᵐᵒᵖ Z]
    (hY : ActionsCommute R S Y)
    {X' : Type 0} {Y' : Type 1} {Z' : Type 0}
    [AddCommGroup X'] [AddCommGroup Y'] [AddCommGroup Z']
    [NonUnitalModule Rᵐᵒᵖ X'] [NonUnitalModule R Y']
    [NonUnitalModule Sᵐᵒᵖ Y'] [NonUnitalModule Sᵐᵒᵖ Z']
    (hY' : ActionsCommute R S Y')
    (f : NonUnitalModuleHom Rᵐᵒᵖ X' X) (g : NonUnitalBimoduleHom R S Y' Y)
    (k : NonUnitalModuleHom Sᵐᵒᵖ Z Z')
    (E : (Right.TensorHom R S X Y Z hY ≃+ Right.CurriedHom R S X Y Z hY)) (E' : (Right.TensorHom R S X' Y' Z' hY' ≃+ Right.CurriedHom R S X' Y' Z' hY')), Prop := @Right.Naturality

example : ∀ (R : Type 1) (S : Type 0) (X : Type 1) (Y : Type 0) (Z : Type 1)
    [NonUnitalRing R] [NonUnitalRing S]
    [AddCommGroup X] [AddCommGroup Y] [AddCommGroup Z]
    [NonUnitalModule Rᵐᵒᵖ X] [NonUnitalModule R Y]
    [NonUnitalModule Sᵐᵒᵖ Y] [NonUnitalModule Sᵐᵒᵖ Z]
    (hY : ActionsCommute R S Y)
    {X' : Type 0} {Y' : Type 1} {Z' : Type 0}
    [AddCommGroup X'] [AddCommGroup Y'] [AddCommGroup Z']
    [NonUnitalModule Rᵐᵒᵖ X'] [NonUnitalModule R Y']
    [NonUnitalModule Sᵐᵒᵖ Y'] [NonUnitalModule Sᵐᵒᵖ Z']
    (hY' : ActionsCommute R S Y')
    (f : NonUnitalModuleHom Rᵐᵒᵖ X' X) (g : NonUnitalBimoduleHom R S Y' Y)
    (k : NonUnitalModuleHom Sᵐᵒᵖ Z Z')
    (hR : IsIdempotented R) (End : (Right.TensorHom R S X Y Z hY ≃+ Right.RefinedHom R S X Y Z hY hR)) (End' : (Right.TensorHom R S X' Y' Z' hY' ≃+ Right.RefinedHom R S X' Y' Z' hY' hR)), Prop := @Right.RefinedNaturality

example : ∀ (R : Type 1) (S : Type 0) (X : Type 1) (Y : Type 0) (Z : Type 1)
    [NonUnitalRing R] [NonUnitalRing S]
    [AddCommGroup X] [AddCommGroup Y] [AddCommGroup Z]
    [NonUnitalModule R X] [NonUnitalModule S Y]
    [NonUnitalModule Rᵐᵒᵖ Y] [NonUnitalModule S Z]
    (hY : ActionsCommute S R Y)
    (E : (Left.TensorHom R S X Y Z hY ≃+ Left.CurriedHom R S X Y Z hY)), Prop := @Left.Canonical

example : ∀ (R : Type 1) (S : Type 0) (X : Type 1) (Y : Type 0) (Z : Type 1)
    [NonUnitalRing R] [NonUnitalRing S]
    [AddCommGroup X] [AddCommGroup Y] [AddCommGroup Z]
    [NonUnitalModule R X] [NonUnitalModule S Y]
    [NonUnitalModule Rᵐᵒᵖ Y] [NonUnitalModule S Z]
    (hY : ActionsCommute S R Y), Prop := @Left.ExistsCanonical

example : ∀ (R : Type 1) (S : Type 0) (X : Type 1) (Y : Type 0) (Z : Type 1)
    [NonUnitalRing R] [NonUnitalRing S]
    [AddCommGroup X] [AddCommGroup Y] [AddCommGroup Z]
    [NonUnitalModule R X] [NonUnitalModule S Y]
    [NonUnitalModule Rᵐᵒᵖ Y] [NonUnitalModule S Z]
    (hY : ActionsCommute S R Y)
    (hR : IsIdempotented R) (E : (Left.TensorHom R S X Y Z hY ≃+ Left.CurriedHom R S X Y Z hY)) (End : (Left.TensorHom R S X Y Z hY ≃+ Left.RefinedHom R S X Y Z hY hR)), Prop := @Left.RefinedCanonical

example : ∀ (R : Type 1) (S : Type 0) (X : Type 1) (Y : Type 0) (Z : Type 1)
    [NonUnitalRing R] [NonUnitalRing S]
    [AddCommGroup X] [AddCommGroup Y] [AddCommGroup Z]
    [NonUnitalModule R X] [NonUnitalModule S Y]
    [NonUnitalModule Rᵐᵒᵖ Y] [NonUnitalModule S Z]
    (hY : ActionsCommute S R Y)
    (hR : IsIdempotented R), Prop := @Left.ExistsRefinedCanonical

example : ∀ (R : Type 1) (S : Type 0) (X : Type 1) (Y : Type 0) (Z : Type 1)
    [NonUnitalRing R] [NonUnitalRing S]
    [AddCommGroup X] [AddCommGroup Y] [AddCommGroup Z]
    [NonUnitalModule R X] [NonUnitalModule S Y]
    [NonUnitalModule Rᵐᵒᵖ Y] [NonUnitalModule S Z]
    (hY : ActionsCommute S R Y)
    {X' : Type 0} {Y' : Type 1} {Z' : Type 0}
    [AddCommGroup X'] [AddCommGroup Y'] [AddCommGroup Z']
    [NonUnitalModule R X'] [NonUnitalModule S Y']
    [NonUnitalModule Rᵐᵒᵖ Y'] [NonUnitalModule S Z']
    (hY' : ActionsCommute S R Y')
    (f : NonUnitalModuleHom R X' X) (g : NonUnitalBimoduleHom S R Y' Y)
    (k : NonUnitalModuleHom S Z Z')
    (E : (Left.TensorHom R S X Y Z hY ≃+ Left.CurriedHom R S X Y Z hY)) (E' : (Left.TensorHom R S X' Y' Z' hY' ≃+ Left.CurriedHom R S X' Y' Z' hY')), Prop := @Left.Naturality

example : ∀ (R : Type 1) (S : Type 0) (X : Type 1) (Y : Type 0) (Z : Type 1)
    [NonUnitalRing R] [NonUnitalRing S]
    [AddCommGroup X] [AddCommGroup Y] [AddCommGroup Z]
    [NonUnitalModule R X] [NonUnitalModule S Y]
    [NonUnitalModule Rᵐᵒᵖ Y] [NonUnitalModule S Z]
    (hY : ActionsCommute S R Y)
    {X' : Type 0} {Y' : Type 1} {Z' : Type 0}
    [AddCommGroup X'] [AddCommGroup Y'] [AddCommGroup Z']
    [NonUnitalModule R X'] [NonUnitalModule S Y']
    [NonUnitalModule Rᵐᵒᵖ Y'] [NonUnitalModule S Z']
    (hY' : ActionsCommute S R Y')
    (f : NonUnitalModuleHom R X' X) (g : NonUnitalBimoduleHom S R Y' Y)
    (k : NonUnitalModuleHom S Z Z')
    (hR : IsIdempotented R) (End : (Left.TensorHom R S X Y Z hY ≃+ Left.RefinedHom R S X Y Z hY hR)) (End' : (Left.TensorHom R S X' Y' Z' hY' ≃+ Left.RefinedHom R S X' Y' Z' hY' hR)), Prop := @Left.RefinedNaturality

example : Prop := Right.ExistenceTheorem.{1, 0, 1, 0, 1}

example : Prop := Right.RefinedExistenceTheorem.{1, 0, 1, 0, 1}

example : Prop := Right.NaturalityTheorem.{1, 0, 1, 0, 1, 0, 1, 0}

example : Prop := Right.RefinedNaturalityTheorem.{1, 0, 1, 0, 1, 0, 1, 0}

example : Prop := Left.ExistenceTheorem.{1, 0, 1, 0, 1}

example : Prop := Left.RefinedExistenceTheorem.{1, 0, 1, 0, 1}

example : Prop := Left.NaturalityTheorem.{1, 0, 1, 0, 1, 0, 1, 0}

example : Prop := Left.RefinedNaturalityTheorem.{1, 0, 1, 0, 1, 0, 1, 0}

example : Prop := NonUnitalTensorHomAdjunctionTheorem.{1, 0, 1, 0, 1, 0, 1, 0}

end Interfaces

section RightUnfoldings

variable (R : Type uR) (S : Type uS) (X : Type uX) (Y : Type uY) (Z : Type uZ)
    [NonUnitalRing R] [NonUnitalRing S]
    [AddCommGroup X] [AddCommGroup Y] [AddCommGroup Z]
    [NonUnitalModule Rᵐᵒᵖ X] [NonUnitalModule R Y]
    [NonUnitalModule Sᵐᵒᵖ Y] [NonUnitalModule Sᵐᵒᵖ Z]
    (hY : ActionsCommute R S Y)

example (E : Right.TensorHom R S X Y Z hY ≃+ Right.CurriedHom R S X Y Z hY) :
    Right.Canonical R S X Y Z hY E =
      (letI := rightModule X hY
       (∀ (φ : Right.TensorHom R S X Y Z hY) (x : X) (y : Y), (E φ x) y = φ (tmul R X Y x y)) ∧
       (∀ ψ : Right.CurriedHom R S X Y Z hY, (E.symm ψ).toAddMonoidHom =
         lift R (Right.evaluationPairing R S X Y Z hY ψ)
           (Right.evaluationPairing_balanced R S X Y Z hY ψ)) ∧
       (∀ (ψ : Right.CurriedHom R S X Y Z hY) (x : X) (y : Y), E.symm ψ (tmul R X Y x y) = (ψ x) y) ∧
       (E.symm.toAddMonoidHom.comp E.toAddMonoidHom = AddMonoidHom.id (Right.TensorHom R S X Y Z hY) ∧
        E.toAddMonoidHom.comp E.symm.toAddMonoidHom = AddMonoidHom.id (Right.CurriedHom R S X Y Z hY))) := rfl

example : Right.ExistsCanonical R S X Y Z hY =
    (∃ E : Right.TensorHom R S X Y Z hY ≃+ Right.CurriedHom R S X Y Z hY, Right.Canonical R S X Y Z hY E) := rfl

example (hR : IsIdempotented R) (E : Right.TensorHom R S X Y Z hY ≃+ Right.CurriedHom R S X Y Z hY)
    (End : Right.TensorHom R S X Y Z hY ≃+ Right.RefinedHom R S X Y Z hY hR) :
    Right.RefinedCanonical R S X Y Z hY hR E End =
      (Right.Canonical R S X Y Z hY E ∧
       (∀ (φ : Right.TensorHom R S X Y Z hY) (x : X) (y : Y), ((End φ x).val) y = φ (tmul R X Y x y)) ∧
       (Right.inclusionMap R S X Y Z hY hR).comp End.toAddMonoidHom = E.toAddMonoidHom ∧
       End.symm.toAddMonoidHom =
         E.symm.toAddMonoidHom.comp (Right.inclusionMap R S X Y Z hY hR)) := rfl

example (hR : IsIdempotented R) :
    Right.ExistsRefinedCanonical R S X Y Z hY hR =
      (∃ (E : Right.TensorHom R S X Y Z hY ≃+ Right.CurriedHom R S X Y Z hY) (End : Right.TensorHom R S X Y Z hY ≃+ Right.RefinedHom R S X Y Z hY hR),
        Right.RefinedCanonical R S X Y Z hY hR E End) := rfl

example (hR : IsIdempotented R) :
    Right.HomPart R S Y Z hY hR =
      (letI := rightSourceAction (Z := Z) hY
       nondegeneratePart hR.op (NonUnitalModuleHom Sᵐᵒᵖ Y Z)) := rfl

example (hR : IsIdempotented R) :
    Right.RefinedHom R S X Y Z hY hR =
      NonUnitalModuleHom Rᵐᵒᵖ X (Right.HomPart R S Y Z hY hR) := rfl

example (hR : IsIdempotented R) :
    Right.inclusionMap R S X Y Z hY hR =
      (letI := rightSourceAction (Z := Z) hY
       postcomposeAddHom (Right.HomPart R S Y Z hY hR).subtype) := rfl

variable {X' : Type uX'} {Y' : Type uY'} {Z' : Type uZ'}
    [AddCommGroup X'] [AddCommGroup Y'] [AddCommGroup Z']
    [NonUnitalModule Rᵐᵒᵖ X'] [NonUnitalModule R Y']
    [NonUnitalModule Sᵐᵒᵖ Y'] [NonUnitalModule Sᵐᵒᵖ Z']
    (hY' : ActionsCommute R S Y')
  (f : NonUnitalModuleHom Rᵐᵒᵖ X' X) (g : NonUnitalBimoduleHom R S Y' Y)
    (k : NonUnitalModuleHom Sᵐᵒᵖ Z Z')

example : Right.tensorHomMap R S X Y Z hY hY' f g k =
    (letI := rightModule X hY
     letI := rightModule X' hY'
     mapAddHom (rightMap hY' hY f g) k) := rfl

example : Right.curriedHomMap R S X Y Z hY hY' f g k =
    (letI := rightSourceAction (Z := Z) hY
     letI := rightSourceAction (Z := Z') hY'
     mapAddHom f (rightSourceMap hY hY' g k)) := rfl

example (hR : IsIdempotented R) :
    Right.refinedHomMap R S X Y Z hY hY' f g k hR =
      (letI := rightSourceAction (Z := Z) hY
       letI := rightSourceAction (Z := Z') hY'
       mapAddHom f ((rightSourceMap hY hY' g k).restrictNondegeneratePart hR.op)) := rfl

example (E : Right.TensorHom R S X Y Z hY ≃+ Right.CurriedHom R S X Y Z hY) (E' : Right.TensorHom R S X' Y' Z' hY' ≃+ Right.CurriedHom R S X' Y' Z' hY') :
    Right.Naturality R S X Y Z hY hY' f g k E E' =
      (E'.toAddMonoidHom.comp (Right.tensorHomMap R S X Y Z hY hY' f g k) =
         (Right.curriedHomMap R S X Y Z hY hY' f g k).comp E.toAddMonoidHom ∧
       E'.symm.toAddMonoidHom.comp (Right.curriedHomMap R S X Y Z hY hY' f g k) =
         (Right.tensorHomMap R S X Y Z hY hY' f g k).comp E.symm.toAddMonoidHom) := rfl

example (hR : IsIdempotented R)
    (End : Right.TensorHom R S X Y Z hY ≃+ Right.RefinedHom R S X Y Z hY hR) (End' : Right.TensorHom R S X' Y' Z' hY' ≃+ Right.RefinedHom R S X' Y' Z' hY' hR) :
    Right.RefinedNaturality R S X Y Z hY hY' f g k hR End End' =
      (End'.toAddMonoidHom.comp (Right.tensorHomMap R S X Y Z hY hY' f g k) =
         (Right.refinedHomMap R S X Y Z hY hY' f g k hR).comp End.toAddMonoidHom ∧
       End'.symm.toAddMonoidHom.comp (Right.refinedHomMap R S X Y Z hY hY' f g k hR) =
         (Right.tensorHomMap R S X Y Z hY hY' f g k).comp End.symm.toAddMonoidHom) := rfl

end RightUnfoldings

section LeftUnfoldings

variable (R : Type uR) (S : Type uS) (X : Type uX) (Y : Type uY) (Z : Type uZ)
    [NonUnitalRing R] [NonUnitalRing S]
    [AddCommGroup X] [AddCommGroup Y] [AddCommGroup Z]
    [NonUnitalModule R X] [NonUnitalModule S Y]
    [NonUnitalModule Rᵐᵒᵖ Y] [NonUnitalModule S Z]
    (hY : ActionsCommute S R Y)

example (E : Left.TensorHom R S X Y Z hY ≃+ Left.CurriedHom R S X Y Z hY) :
    Left.Canonical R S X Y Z hY E =
      (letI := leftModule hY X
       (∀ (φ : Left.TensorHom R S X Y Z hY) (x : X) (y : Y), (E φ x) y = φ (tmul R Y X y x)) ∧
       (∀ ψ : Left.CurriedHom R S X Y Z hY, (E.symm ψ).toAddMonoidHom =
         lift R (Left.evaluationPairing R S X Y Z hY ψ)
           (Left.evaluationPairing_balanced R S X Y Z hY ψ)) ∧
       (∀ (ψ : Left.CurriedHom R S X Y Z hY) (x : X) (y : Y), E.symm ψ (tmul R Y X y x) = (ψ x) y) ∧
       (E.symm.toAddMonoidHom.comp E.toAddMonoidHom = AddMonoidHom.id (Left.TensorHom R S X Y Z hY) ∧
        E.toAddMonoidHom.comp E.symm.toAddMonoidHom = AddMonoidHom.id (Left.CurriedHom R S X Y Z hY))) := rfl

example : Left.ExistsCanonical R S X Y Z hY =
    (∃ E : Left.TensorHom R S X Y Z hY ≃+ Left.CurriedHom R S X Y Z hY, Left.Canonical R S X Y Z hY E) := rfl

example (hR : IsIdempotented R) (E : Left.TensorHom R S X Y Z hY ≃+ Left.CurriedHom R S X Y Z hY)
    (End : Left.TensorHom R S X Y Z hY ≃+ Left.RefinedHom R S X Y Z hY hR) :
    Left.RefinedCanonical R S X Y Z hY hR E End =
      (Left.Canonical R S X Y Z hY E ∧
       (∀ (φ : Left.TensorHom R S X Y Z hY) (x : X) (y : Y), ((End φ x).val) y = φ (tmul R Y X y x)) ∧
       (Left.inclusionMap R S X Y Z hY hR).comp End.toAddMonoidHom = E.toAddMonoidHom ∧
       End.symm.toAddMonoidHom =
         E.symm.toAddMonoidHom.comp (Left.inclusionMap R S X Y Z hY hR)) := rfl

example (hR : IsIdempotented R) :
    Left.ExistsRefinedCanonical R S X Y Z hY hR =
      (∃ (E : Left.TensorHom R S X Y Z hY ≃+ Left.CurriedHom R S X Y Z hY) (End : Left.TensorHom R S X Y Z hY ≃+ Left.RefinedHom R S X Y Z hY hR),
        Left.RefinedCanonical R S X Y Z hY hR E End) := rfl

example (hR : IsIdempotented R) :
    Left.HomPart R S Y Z hY hR =
      (letI := sourceAction (Z := Z) hY
       nondegeneratePart hR (NonUnitalModuleHom S Y Z)) := rfl

example (hR : IsIdempotented R) :
    Left.RefinedHom R S X Y Z hY hR =
      NonUnitalModuleHom R X (Left.HomPart R S Y Z hY hR) := rfl

example (hR : IsIdempotented R) :
    Left.inclusionMap R S X Y Z hY hR =
      (letI := sourceAction (Z := Z) hY
       postcomposeAddHom (Left.HomPart R S Y Z hY hR).subtype) := rfl

variable {X' : Type uX'} {Y' : Type uY'} {Z' : Type uZ'}
    [AddCommGroup X'] [AddCommGroup Y'] [AddCommGroup Z']
    [NonUnitalModule R X'] [NonUnitalModule S Y']
    [NonUnitalModule Rᵐᵒᵖ Y'] [NonUnitalModule S Z']
    (hY' : ActionsCommute S R Y')
  (f : NonUnitalModuleHom R X' X) (g : NonUnitalBimoduleHom S R Y' Y)
    (k : NonUnitalModuleHom S Z Z')

example : Left.tensorHomMap R S X Y Z hY hY' f g k =
    (letI := leftModule hY X
     letI := leftModule hY' X'
     mapAddHom (leftMap hY' hY g f) k) := rfl

example : Left.curriedHomMap R S X Y Z hY hY' f g k =
    (letI := sourceAction (Z := Z) hY
     letI := sourceAction (Z := Z') hY'
     mapAddHom f (sourceMap hY hY' g k)) := rfl

example (hR : IsIdempotented R) :
    Left.refinedHomMap R S X Y Z hY hY' f g k hR =
      (letI := sourceAction (Z := Z) hY
       letI := sourceAction (Z := Z') hY'
       mapAddHom f ((sourceMap hY hY' g k).restrictNondegeneratePart hR)) := rfl

example (E : Left.TensorHom R S X Y Z hY ≃+ Left.CurriedHom R S X Y Z hY) (E' : Left.TensorHom R S X' Y' Z' hY' ≃+ Left.CurriedHom R S X' Y' Z' hY') :
    Left.Naturality R S X Y Z hY hY' f g k E E' =
      (E'.toAddMonoidHom.comp (Left.tensorHomMap R S X Y Z hY hY' f g k) =
         (Left.curriedHomMap R S X Y Z hY hY' f g k).comp E.toAddMonoidHom ∧
       E'.symm.toAddMonoidHom.comp (Left.curriedHomMap R S X Y Z hY hY' f g k) =
         (Left.tensorHomMap R S X Y Z hY hY' f g k).comp E.symm.toAddMonoidHom) := rfl

example (hR : IsIdempotented R)
    (End : Left.TensorHom R S X Y Z hY ≃+ Left.RefinedHom R S X Y Z hY hR) (End' : Left.TensorHom R S X' Y' Z' hY' ≃+ Left.RefinedHom R S X' Y' Z' hY' hR) :
    Left.RefinedNaturality R S X Y Z hY hY' f g k hR End End' =
      (End'.toAddMonoidHom.comp (Left.tensorHomMap R S X Y Z hY hY' f g k) =
         (Left.refinedHomMap R S X Y Z hY hY' f g k hR).comp End.toAddMonoidHom ∧
       End'.symm.toAddMonoidHom.comp (Left.refinedHomMap R S X Y Z hY hY' f g k hR) =
         (Left.tensorHomMap R S X Y Z hY hY' f g k).comp End.symm.toAddMonoidHom) := rfl

end LeftUnfoldings

/-! Closed exact unfoldings at Arbitrary universes. -/

example : Right.ExistenceTheorem.{uR, uS, uX, uY, uZ} =
    (∀ (R : Type uR) (S : Type uS) (X : Type uX) (Y : Type uY) (Z : Type uZ)
    [NonUnitalRing R] [NonUnitalRing S]
    [AddCommGroup X] [AddCommGroup Y] [AddCommGroup Z]
    [NonUnitalModule Rᵐᵒᵖ X] [NonUnitalModule R Y]
    [NonUnitalModule Sᵐᵒᵖ Y] [NonUnitalModule Sᵐᵒᵖ Z]
    (hY : ActionsCommute R S Y), Right.ExistsCanonical R S X Y Z hY) := rfl

example : Right.RefinedExistenceTheorem.{uR, uS, uX, uY, uZ} =
    (∀ (R : Type uR) (S : Type uS) (X : Type uX) (Y : Type uY) (Z : Type uZ)
    [NonUnitalRing R] [NonUnitalRing S]
    [AddCommGroup X] [AddCommGroup Y] [AddCommGroup Z]
    [NonUnitalModule Rᵐᵒᵖ X] [NonUnitalModule R Y]
    [NonUnitalModule Sᵐᵒᵖ Y] [NonUnitalModule Sᵐᵒᵖ Z]
    (hY : ActionsCommute R S Y) (hR : IsIdempotented R),
      IsNondegenerate Rᵐᵒᵖ X → Right.ExistsRefinedCanonical R S X Y Z hY hR) := rfl

example : Right.NaturalityTheorem.{uR, uS, uX, uY, uZ, uX', uY', uZ'} =
    (∀ (R : Type uR) (S : Type uS) (X : Type uX) (Y : Type uY) (Z : Type uZ)
      (X' : Type uX') (Y' : Type uY') (Z' : Type uZ')
      [NonUnitalRing R] [NonUnitalRing S]
      [AddCommGroup X] [AddCommGroup Y] [AddCommGroup Z]
      [AddCommGroup X'] [AddCommGroup Y'] [AddCommGroup Z']
      [NonUnitalModule Rᵐᵒᵖ X] [NonUnitalModule R Y]
      [NonUnitalModule Sᵐᵒᵖ Y] [NonUnitalModule Sᵐᵒᵖ Z]
      [NonUnitalModule Rᵐᵒᵖ X'] [NonUnitalModule R Y']
      [NonUnitalModule Sᵐᵒᵖ Y'] [NonUnitalModule Sᵐᵒᵖ Z']
      (hY : ActionsCommute R S Y) (hY' : ActionsCommute R S Y')
      (f : NonUnitalModuleHom Rᵐᵒᵖ X' X) (g : NonUnitalBimoduleHom R S Y' Y)
    (k : NonUnitalModuleHom Sᵐᵒᵖ Z Z')
      (E : Right.TensorHom R S X Y Z hY ≃+ Right.CurriedHom R S X Y Z hY) (E' : Right.TensorHom R S X' Y' Z' hY' ≃+ Right.CurriedHom R S X' Y' Z' hY'),
      Right.Canonical R S X Y Z hY E → Right.Canonical R S X' Y' Z' hY' E' →
        Right.Naturality R S X Y Z hY hY' f g k E E') := rfl

example : Right.RefinedNaturalityTheorem.{uR, uS, uX, uY, uZ, uX', uY', uZ'} =
    (∀ (R : Type uR) (S : Type uS) (X : Type uX) (Y : Type uY) (Z : Type uZ)
      (X' : Type uX') (Y' : Type uY') (Z' : Type uZ')
      [NonUnitalRing R] [NonUnitalRing S]
      [AddCommGroup X] [AddCommGroup Y] [AddCommGroup Z]
      [AddCommGroup X'] [AddCommGroup Y'] [AddCommGroup Z']
      [NonUnitalModule Rᵐᵒᵖ X] [NonUnitalModule R Y]
      [NonUnitalModule Sᵐᵒᵖ Y] [NonUnitalModule Sᵐᵒᵖ Z]
      [NonUnitalModule Rᵐᵒᵖ X'] [NonUnitalModule R Y']
      [NonUnitalModule Sᵐᵒᵖ Y'] [NonUnitalModule Sᵐᵒᵖ Z']
      (hY : ActionsCommute R S Y) (hY' : ActionsCommute R S Y')
      (hR : IsIdempotented R) (f : NonUnitalModuleHom Rᵐᵒᵖ X' X) (g : NonUnitalBimoduleHom R S Y' Y)
    (k : NonUnitalModuleHom Sᵐᵒᵖ Z Z')
      (E : Right.TensorHom R S X Y Z hY ≃+ Right.CurriedHom R S X Y Z hY) (E' : Right.TensorHom R S X' Y' Z' hY' ≃+ Right.CurriedHom R S X' Y' Z' hY')
      (End : Right.TensorHom R S X Y Z hY ≃+ Right.RefinedHom R S X Y Z hY hR) (End' : Right.TensorHom R S X' Y' Z' hY' ≃+ Right.RefinedHom R S X' Y' Z' hY' hR),
      IsNondegenerate Rᵐᵒᵖ X → IsNondegenerate Rᵐᵒᵖ X' →
        Right.RefinedCanonical R S X Y Z hY hR E End →
        Right.RefinedCanonical R S X' Y' Z' hY' hR E' End' →
        Right.RefinedNaturality R S X Y Z hY hY' f g k hR End End') := rfl

example : Left.ExistenceTheorem.{uR, uS, uX, uY, uZ} =
    (∀ (R : Type uR) (S : Type uS) (X : Type uX) (Y : Type uY) (Z : Type uZ)
    [NonUnitalRing R] [NonUnitalRing S]
    [AddCommGroup X] [AddCommGroup Y] [AddCommGroup Z]
    [NonUnitalModule R X] [NonUnitalModule S Y]
    [NonUnitalModule Rᵐᵒᵖ Y] [NonUnitalModule S Z]
    (hY : ActionsCommute S R Y), Left.ExistsCanonical R S X Y Z hY) := rfl

example : Left.RefinedExistenceTheorem.{uR, uS, uX, uY, uZ} =
    (∀ (R : Type uR) (S : Type uS) (X : Type uX) (Y : Type uY) (Z : Type uZ)
    [NonUnitalRing R] [NonUnitalRing S]
    [AddCommGroup X] [AddCommGroup Y] [AddCommGroup Z]
    [NonUnitalModule R X] [NonUnitalModule S Y]
    [NonUnitalModule Rᵐᵒᵖ Y] [NonUnitalModule S Z]
    (hY : ActionsCommute S R Y) (hR : IsIdempotented R),
      IsNondegenerate R X → Left.ExistsRefinedCanonical R S X Y Z hY hR) := rfl

example : Left.NaturalityTheorem.{uR, uS, uX, uY, uZ, uX', uY', uZ'} =
    (∀ (R : Type uR) (S : Type uS) (X : Type uX) (Y : Type uY) (Z : Type uZ)
      (X' : Type uX') (Y' : Type uY') (Z' : Type uZ')
      [NonUnitalRing R] [NonUnitalRing S]
      [AddCommGroup X] [AddCommGroup Y] [AddCommGroup Z]
      [AddCommGroup X'] [AddCommGroup Y'] [AddCommGroup Z']
      [NonUnitalModule R X] [NonUnitalModule S Y]
      [NonUnitalModule Rᵐᵒᵖ Y] [NonUnitalModule S Z]
      [NonUnitalModule R X'] [NonUnitalModule S Y']
      [NonUnitalModule Rᵐᵒᵖ Y'] [NonUnitalModule S Z']
      (hY : ActionsCommute S R Y) (hY' : ActionsCommute S R Y')
      (f : NonUnitalModuleHom R X' X) (g : NonUnitalBimoduleHom S R Y' Y)
    (k : NonUnitalModuleHom S Z Z')
      (E : Left.TensorHom R S X Y Z hY ≃+ Left.CurriedHom R S X Y Z hY) (E' : Left.TensorHom R S X' Y' Z' hY' ≃+ Left.CurriedHom R S X' Y' Z' hY'),
      Left.Canonical R S X Y Z hY E → Left.Canonical R S X' Y' Z' hY' E' →
        Left.Naturality R S X Y Z hY hY' f g k E E') := rfl

example : Left.RefinedNaturalityTheorem.{uR, uS, uX, uY, uZ, uX', uY', uZ'} =
    (∀ (R : Type uR) (S : Type uS) (X : Type uX) (Y : Type uY) (Z : Type uZ)
      (X' : Type uX') (Y' : Type uY') (Z' : Type uZ')
      [NonUnitalRing R] [NonUnitalRing S]
      [AddCommGroup X] [AddCommGroup Y] [AddCommGroup Z]
      [AddCommGroup X'] [AddCommGroup Y'] [AddCommGroup Z']
      [NonUnitalModule R X] [NonUnitalModule S Y]
      [NonUnitalModule Rᵐᵒᵖ Y] [NonUnitalModule S Z]
      [NonUnitalModule R X'] [NonUnitalModule S Y']
      [NonUnitalModule Rᵐᵒᵖ Y'] [NonUnitalModule S Z']
      (hY : ActionsCommute S R Y) (hY' : ActionsCommute S R Y')
      (hR : IsIdempotented R) (f : NonUnitalModuleHom R X' X) (g : NonUnitalBimoduleHom S R Y' Y)
    (k : NonUnitalModuleHom S Z Z')
      (E : Left.TensorHom R S X Y Z hY ≃+ Left.CurriedHom R S X Y Z hY) (E' : Left.TensorHom R S X' Y' Z' hY' ≃+ Left.CurriedHom R S X' Y' Z' hY')
      (End : Left.TensorHom R S X Y Z hY ≃+ Left.RefinedHom R S X Y Z hY hR) (End' : Left.TensorHom R S X' Y' Z' hY' ≃+ Left.RefinedHom R S X' Y' Z' hY' hR),
      IsNondegenerate R X → IsNondegenerate R X' →
        Left.RefinedCanonical R S X Y Z hY hR E End →
        Left.RefinedCanonical R S X' Y' Z' hY' hR E' End' →
        Left.RefinedNaturality R S X Y Z hY hY' f g k hR End End') := rfl

example : NonUnitalTensorHomAdjunctionTheorem.{uR, uS, uX, uY, uZ, uX', uY', uZ'} =
    (Right.ExistenceTheorem.{uR, uS, uX, uY, uZ} ∧ Left.ExistenceTheorem.{uR, uS, uX, uY, uZ} ∧
     Right.NaturalityTheorem.{uR, uS, uX, uY, uZ, uX', uY', uZ'} ∧ Left.NaturalityTheorem.{uR, uS, uX, uY, uZ, uX', uY', uZ'} ∧
     Right.RefinedExistenceTheorem.{uR, uS, uX, uY, uZ} ∧ Left.RefinedExistenceTheorem.{uR, uS, uX, uY, uZ} ∧
     Right.RefinedNaturalityTheorem.{uR, uS, uX, uY, uZ, uX', uY', uZ'} ∧ Left.RefinedNaturalityTheorem.{uR, uS, uX, uY, uZ, uX', uY', uZ'}) := rfl

/-! Closed exact unfoldings at SmallLarge universes. -/

example : Right.ExistenceTheorem.{0, 1, 0, 1, 0} =
    (∀ (R : Type 0) (S : Type 1) (X : Type 0) (Y : Type 1) (Z : Type 0)
    [NonUnitalRing R] [NonUnitalRing S]
    [AddCommGroup X] [AddCommGroup Y] [AddCommGroup Z]
    [NonUnitalModule Rᵐᵒᵖ X] [NonUnitalModule R Y]
    [NonUnitalModule Sᵐᵒᵖ Y] [NonUnitalModule Sᵐᵒᵖ Z]
    (hY : ActionsCommute R S Y), Right.ExistsCanonical R S X Y Z hY) := rfl

example : Right.RefinedExistenceTheorem.{0, 1, 0, 1, 0} =
    (∀ (R : Type 0) (S : Type 1) (X : Type 0) (Y : Type 1) (Z : Type 0)
    [NonUnitalRing R] [NonUnitalRing S]
    [AddCommGroup X] [AddCommGroup Y] [AddCommGroup Z]
    [NonUnitalModule Rᵐᵒᵖ X] [NonUnitalModule R Y]
    [NonUnitalModule Sᵐᵒᵖ Y] [NonUnitalModule Sᵐᵒᵖ Z]
    (hY : ActionsCommute R S Y) (hR : IsIdempotented R),
      IsNondegenerate Rᵐᵒᵖ X → Right.ExistsRefinedCanonical R S X Y Z hY hR) := rfl

example : Right.NaturalityTheorem.{0, 1, 0, 1, 0, 1, 0, 1} =
    (∀ (R : Type 0) (S : Type 1) (X : Type 0) (Y : Type 1) (Z : Type 0)
      (X' : Type 1) (Y' : Type 0) (Z' : Type 1)
      [NonUnitalRing R] [NonUnitalRing S]
      [AddCommGroup X] [AddCommGroup Y] [AddCommGroup Z]
      [AddCommGroup X'] [AddCommGroup Y'] [AddCommGroup Z']
      [NonUnitalModule Rᵐᵒᵖ X] [NonUnitalModule R Y]
      [NonUnitalModule Sᵐᵒᵖ Y] [NonUnitalModule Sᵐᵒᵖ Z]
      [NonUnitalModule Rᵐᵒᵖ X'] [NonUnitalModule R Y']
      [NonUnitalModule Sᵐᵒᵖ Y'] [NonUnitalModule Sᵐᵒᵖ Z']
      (hY : ActionsCommute R S Y) (hY' : ActionsCommute R S Y')
      (f : NonUnitalModuleHom Rᵐᵒᵖ X' X) (g : NonUnitalBimoduleHom R S Y' Y)
    (k : NonUnitalModuleHom Sᵐᵒᵖ Z Z')
      (E : Right.TensorHom R S X Y Z hY ≃+ Right.CurriedHom R S X Y Z hY) (E' : Right.TensorHom R S X' Y' Z' hY' ≃+ Right.CurriedHom R S X' Y' Z' hY'),
      Right.Canonical R S X Y Z hY E → Right.Canonical R S X' Y' Z' hY' E' →
        Right.Naturality R S X Y Z hY hY' f g k E E') := rfl

example : Right.RefinedNaturalityTheorem.{0, 1, 0, 1, 0, 1, 0, 1} =
    (∀ (R : Type 0) (S : Type 1) (X : Type 0) (Y : Type 1) (Z : Type 0)
      (X' : Type 1) (Y' : Type 0) (Z' : Type 1)
      [NonUnitalRing R] [NonUnitalRing S]
      [AddCommGroup X] [AddCommGroup Y] [AddCommGroup Z]
      [AddCommGroup X'] [AddCommGroup Y'] [AddCommGroup Z']
      [NonUnitalModule Rᵐᵒᵖ X] [NonUnitalModule R Y]
      [NonUnitalModule Sᵐᵒᵖ Y] [NonUnitalModule Sᵐᵒᵖ Z]
      [NonUnitalModule Rᵐᵒᵖ X'] [NonUnitalModule R Y']
      [NonUnitalModule Sᵐᵒᵖ Y'] [NonUnitalModule Sᵐᵒᵖ Z']
      (hY : ActionsCommute R S Y) (hY' : ActionsCommute R S Y')
      (hR : IsIdempotented R) (f : NonUnitalModuleHom Rᵐᵒᵖ X' X) (g : NonUnitalBimoduleHom R S Y' Y)
    (k : NonUnitalModuleHom Sᵐᵒᵖ Z Z')
      (E : Right.TensorHom R S X Y Z hY ≃+ Right.CurriedHom R S X Y Z hY) (E' : Right.TensorHom R S X' Y' Z' hY' ≃+ Right.CurriedHom R S X' Y' Z' hY')
      (End : Right.TensorHom R S X Y Z hY ≃+ Right.RefinedHom R S X Y Z hY hR) (End' : Right.TensorHom R S X' Y' Z' hY' ≃+ Right.RefinedHom R S X' Y' Z' hY' hR),
      IsNondegenerate Rᵐᵒᵖ X → IsNondegenerate Rᵐᵒᵖ X' →
        Right.RefinedCanonical R S X Y Z hY hR E End →
        Right.RefinedCanonical R S X' Y' Z' hY' hR E' End' →
        Right.RefinedNaturality R S X Y Z hY hY' f g k hR End End') := rfl

example : Left.ExistenceTheorem.{0, 1, 0, 1, 0} =
    (∀ (R : Type 0) (S : Type 1) (X : Type 0) (Y : Type 1) (Z : Type 0)
    [NonUnitalRing R] [NonUnitalRing S]
    [AddCommGroup X] [AddCommGroup Y] [AddCommGroup Z]
    [NonUnitalModule R X] [NonUnitalModule S Y]
    [NonUnitalModule Rᵐᵒᵖ Y] [NonUnitalModule S Z]
    (hY : ActionsCommute S R Y), Left.ExistsCanonical R S X Y Z hY) := rfl

example : Left.RefinedExistenceTheorem.{0, 1, 0, 1, 0} =
    (∀ (R : Type 0) (S : Type 1) (X : Type 0) (Y : Type 1) (Z : Type 0)
    [NonUnitalRing R] [NonUnitalRing S]
    [AddCommGroup X] [AddCommGroup Y] [AddCommGroup Z]
    [NonUnitalModule R X] [NonUnitalModule S Y]
    [NonUnitalModule Rᵐᵒᵖ Y] [NonUnitalModule S Z]
    (hY : ActionsCommute S R Y) (hR : IsIdempotented R),
      IsNondegenerate R X → Left.ExistsRefinedCanonical R S X Y Z hY hR) := rfl

example : Left.NaturalityTheorem.{0, 1, 0, 1, 0, 1, 0, 1} =
    (∀ (R : Type 0) (S : Type 1) (X : Type 0) (Y : Type 1) (Z : Type 0)
      (X' : Type 1) (Y' : Type 0) (Z' : Type 1)
      [NonUnitalRing R] [NonUnitalRing S]
      [AddCommGroup X] [AddCommGroup Y] [AddCommGroup Z]
      [AddCommGroup X'] [AddCommGroup Y'] [AddCommGroup Z']
      [NonUnitalModule R X] [NonUnitalModule S Y]
      [NonUnitalModule Rᵐᵒᵖ Y] [NonUnitalModule S Z]
      [NonUnitalModule R X'] [NonUnitalModule S Y']
      [NonUnitalModule Rᵐᵒᵖ Y'] [NonUnitalModule S Z']
      (hY : ActionsCommute S R Y) (hY' : ActionsCommute S R Y')
      (f : NonUnitalModuleHom R X' X) (g : NonUnitalBimoduleHom S R Y' Y)
    (k : NonUnitalModuleHom S Z Z')
      (E : Left.TensorHom R S X Y Z hY ≃+ Left.CurriedHom R S X Y Z hY) (E' : Left.TensorHom R S X' Y' Z' hY' ≃+ Left.CurriedHom R S X' Y' Z' hY'),
      Left.Canonical R S X Y Z hY E → Left.Canonical R S X' Y' Z' hY' E' →
        Left.Naturality R S X Y Z hY hY' f g k E E') := rfl

example : Left.RefinedNaturalityTheorem.{0, 1, 0, 1, 0, 1, 0, 1} =
    (∀ (R : Type 0) (S : Type 1) (X : Type 0) (Y : Type 1) (Z : Type 0)
      (X' : Type 1) (Y' : Type 0) (Z' : Type 1)
      [NonUnitalRing R] [NonUnitalRing S]
      [AddCommGroup X] [AddCommGroup Y] [AddCommGroup Z]
      [AddCommGroup X'] [AddCommGroup Y'] [AddCommGroup Z']
      [NonUnitalModule R X] [NonUnitalModule S Y]
      [NonUnitalModule Rᵐᵒᵖ Y] [NonUnitalModule S Z]
      [NonUnitalModule R X'] [NonUnitalModule S Y']
      [NonUnitalModule Rᵐᵒᵖ Y'] [NonUnitalModule S Z']
      (hY : ActionsCommute S R Y) (hY' : ActionsCommute S R Y')
      (hR : IsIdempotented R) (f : NonUnitalModuleHom R X' X) (g : NonUnitalBimoduleHom S R Y' Y)
    (k : NonUnitalModuleHom S Z Z')
      (E : Left.TensorHom R S X Y Z hY ≃+ Left.CurriedHom R S X Y Z hY) (E' : Left.TensorHom R S X' Y' Z' hY' ≃+ Left.CurriedHom R S X' Y' Z' hY')
      (End : Left.TensorHom R S X Y Z hY ≃+ Left.RefinedHom R S X Y Z hY hR) (End' : Left.TensorHom R S X' Y' Z' hY' ≃+ Left.RefinedHom R S X' Y' Z' hY' hR),
      IsNondegenerate R X → IsNondegenerate R X' →
        Left.RefinedCanonical R S X Y Z hY hR E End →
        Left.RefinedCanonical R S X' Y' Z' hY' hR E' End' →
        Left.RefinedNaturality R S X Y Z hY hY' f g k hR End End') := rfl

example : NonUnitalTensorHomAdjunctionTheorem.{0, 1, 0, 1, 0, 1, 0, 1} =
    (Right.ExistenceTheorem.{0, 1, 0, 1, 0} ∧ Left.ExistenceTheorem.{0, 1, 0, 1, 0} ∧
     Right.NaturalityTheorem.{0, 1, 0, 1, 0, 1, 0, 1} ∧ Left.NaturalityTheorem.{0, 1, 0, 1, 0, 1, 0, 1} ∧
     Right.RefinedExistenceTheorem.{0, 1, 0, 1, 0} ∧ Left.RefinedExistenceTheorem.{0, 1, 0, 1, 0} ∧
     Right.RefinedNaturalityTheorem.{0, 1, 0, 1, 0, 1, 0, 1} ∧ Left.RefinedNaturalityTheorem.{0, 1, 0, 1, 0, 1, 0, 1}) := rfl

/-! Closed exact unfoldings at LargeSmall universes. -/

example : Right.ExistenceTheorem.{1, 0, 1, 0, 1} =
    (∀ (R : Type 1) (S : Type 0) (X : Type 1) (Y : Type 0) (Z : Type 1)
    [NonUnitalRing R] [NonUnitalRing S]
    [AddCommGroup X] [AddCommGroup Y] [AddCommGroup Z]
    [NonUnitalModule Rᵐᵒᵖ X] [NonUnitalModule R Y]
    [NonUnitalModule Sᵐᵒᵖ Y] [NonUnitalModule Sᵐᵒᵖ Z]
    (hY : ActionsCommute R S Y), Right.ExistsCanonical R S X Y Z hY) := rfl

example : Right.RefinedExistenceTheorem.{1, 0, 1, 0, 1} =
    (∀ (R : Type 1) (S : Type 0) (X : Type 1) (Y : Type 0) (Z : Type 1)
    [NonUnitalRing R] [NonUnitalRing S]
    [AddCommGroup X] [AddCommGroup Y] [AddCommGroup Z]
    [NonUnitalModule Rᵐᵒᵖ X] [NonUnitalModule R Y]
    [NonUnitalModule Sᵐᵒᵖ Y] [NonUnitalModule Sᵐᵒᵖ Z]
    (hY : ActionsCommute R S Y) (hR : IsIdempotented R),
      IsNondegenerate Rᵐᵒᵖ X → Right.ExistsRefinedCanonical R S X Y Z hY hR) := rfl

example : Right.NaturalityTheorem.{1, 0, 1, 0, 1, 0, 1, 0} =
    (∀ (R : Type 1) (S : Type 0) (X : Type 1) (Y : Type 0) (Z : Type 1)
      (X' : Type 0) (Y' : Type 1) (Z' : Type 0)
      [NonUnitalRing R] [NonUnitalRing S]
      [AddCommGroup X] [AddCommGroup Y] [AddCommGroup Z]
      [AddCommGroup X'] [AddCommGroup Y'] [AddCommGroup Z']
      [NonUnitalModule Rᵐᵒᵖ X] [NonUnitalModule R Y]
      [NonUnitalModule Sᵐᵒᵖ Y] [NonUnitalModule Sᵐᵒᵖ Z]
      [NonUnitalModule Rᵐᵒᵖ X'] [NonUnitalModule R Y']
      [NonUnitalModule Sᵐᵒᵖ Y'] [NonUnitalModule Sᵐᵒᵖ Z']
      (hY : ActionsCommute R S Y) (hY' : ActionsCommute R S Y')
      (f : NonUnitalModuleHom Rᵐᵒᵖ X' X) (g : NonUnitalBimoduleHom R S Y' Y)
    (k : NonUnitalModuleHom Sᵐᵒᵖ Z Z')
      (E : Right.TensorHom R S X Y Z hY ≃+ Right.CurriedHom R S X Y Z hY) (E' : Right.TensorHom R S X' Y' Z' hY' ≃+ Right.CurriedHom R S X' Y' Z' hY'),
      Right.Canonical R S X Y Z hY E → Right.Canonical R S X' Y' Z' hY' E' →
        Right.Naturality R S X Y Z hY hY' f g k E E') := rfl

example : Right.RefinedNaturalityTheorem.{1, 0, 1, 0, 1, 0, 1, 0} =
    (∀ (R : Type 1) (S : Type 0) (X : Type 1) (Y : Type 0) (Z : Type 1)
      (X' : Type 0) (Y' : Type 1) (Z' : Type 0)
      [NonUnitalRing R] [NonUnitalRing S]
      [AddCommGroup X] [AddCommGroup Y] [AddCommGroup Z]
      [AddCommGroup X'] [AddCommGroup Y'] [AddCommGroup Z']
      [NonUnitalModule Rᵐᵒᵖ X] [NonUnitalModule R Y]
      [NonUnitalModule Sᵐᵒᵖ Y] [NonUnitalModule Sᵐᵒᵖ Z]
      [NonUnitalModule Rᵐᵒᵖ X'] [NonUnitalModule R Y']
      [NonUnitalModule Sᵐᵒᵖ Y'] [NonUnitalModule Sᵐᵒᵖ Z']
      (hY : ActionsCommute R S Y) (hY' : ActionsCommute R S Y')
      (hR : IsIdempotented R) (f : NonUnitalModuleHom Rᵐᵒᵖ X' X) (g : NonUnitalBimoduleHom R S Y' Y)
    (k : NonUnitalModuleHom Sᵐᵒᵖ Z Z')
      (E : Right.TensorHom R S X Y Z hY ≃+ Right.CurriedHom R S X Y Z hY) (E' : Right.TensorHom R S X' Y' Z' hY' ≃+ Right.CurriedHom R S X' Y' Z' hY')
      (End : Right.TensorHom R S X Y Z hY ≃+ Right.RefinedHom R S X Y Z hY hR) (End' : Right.TensorHom R S X' Y' Z' hY' ≃+ Right.RefinedHom R S X' Y' Z' hY' hR),
      IsNondegenerate Rᵐᵒᵖ X → IsNondegenerate Rᵐᵒᵖ X' →
        Right.RefinedCanonical R S X Y Z hY hR E End →
        Right.RefinedCanonical R S X' Y' Z' hY' hR E' End' →
        Right.RefinedNaturality R S X Y Z hY hY' f g k hR End End') := rfl

example : Left.ExistenceTheorem.{1, 0, 1, 0, 1} =
    (∀ (R : Type 1) (S : Type 0) (X : Type 1) (Y : Type 0) (Z : Type 1)
    [NonUnitalRing R] [NonUnitalRing S]
    [AddCommGroup X] [AddCommGroup Y] [AddCommGroup Z]
    [NonUnitalModule R X] [NonUnitalModule S Y]
    [NonUnitalModule Rᵐᵒᵖ Y] [NonUnitalModule S Z]
    (hY : ActionsCommute S R Y), Left.ExistsCanonical R S X Y Z hY) := rfl

example : Left.RefinedExistenceTheorem.{1, 0, 1, 0, 1} =
    (∀ (R : Type 1) (S : Type 0) (X : Type 1) (Y : Type 0) (Z : Type 1)
    [NonUnitalRing R] [NonUnitalRing S]
    [AddCommGroup X] [AddCommGroup Y] [AddCommGroup Z]
    [NonUnitalModule R X] [NonUnitalModule S Y]
    [NonUnitalModule Rᵐᵒᵖ Y] [NonUnitalModule S Z]
    (hY : ActionsCommute S R Y) (hR : IsIdempotented R),
      IsNondegenerate R X → Left.ExistsRefinedCanonical R S X Y Z hY hR) := rfl

example : Left.NaturalityTheorem.{1, 0, 1, 0, 1, 0, 1, 0} =
    (∀ (R : Type 1) (S : Type 0) (X : Type 1) (Y : Type 0) (Z : Type 1)
      (X' : Type 0) (Y' : Type 1) (Z' : Type 0)
      [NonUnitalRing R] [NonUnitalRing S]
      [AddCommGroup X] [AddCommGroup Y] [AddCommGroup Z]
      [AddCommGroup X'] [AddCommGroup Y'] [AddCommGroup Z']
      [NonUnitalModule R X] [NonUnitalModule S Y]
      [NonUnitalModule Rᵐᵒᵖ Y] [NonUnitalModule S Z]
      [NonUnitalModule R X'] [NonUnitalModule S Y']
      [NonUnitalModule Rᵐᵒᵖ Y'] [NonUnitalModule S Z']
      (hY : ActionsCommute S R Y) (hY' : ActionsCommute S R Y')
      (f : NonUnitalModuleHom R X' X) (g : NonUnitalBimoduleHom S R Y' Y)
    (k : NonUnitalModuleHom S Z Z')
      (E : Left.TensorHom R S X Y Z hY ≃+ Left.CurriedHom R S X Y Z hY) (E' : Left.TensorHom R S X' Y' Z' hY' ≃+ Left.CurriedHom R S X' Y' Z' hY'),
      Left.Canonical R S X Y Z hY E → Left.Canonical R S X' Y' Z' hY' E' →
        Left.Naturality R S X Y Z hY hY' f g k E E') := rfl

example : Left.RefinedNaturalityTheorem.{1, 0, 1, 0, 1, 0, 1, 0} =
    (∀ (R : Type 1) (S : Type 0) (X : Type 1) (Y : Type 0) (Z : Type 1)
      (X' : Type 0) (Y' : Type 1) (Z' : Type 0)
      [NonUnitalRing R] [NonUnitalRing S]
      [AddCommGroup X] [AddCommGroup Y] [AddCommGroup Z]
      [AddCommGroup X'] [AddCommGroup Y'] [AddCommGroup Z']
      [NonUnitalModule R X] [NonUnitalModule S Y]
      [NonUnitalModule Rᵐᵒᵖ Y] [NonUnitalModule S Z]
      [NonUnitalModule R X'] [NonUnitalModule S Y']
      [NonUnitalModule Rᵐᵒᵖ Y'] [NonUnitalModule S Z']
      (hY : ActionsCommute S R Y) (hY' : ActionsCommute S R Y')
      (hR : IsIdempotented R) (f : NonUnitalModuleHom R X' X) (g : NonUnitalBimoduleHom S R Y' Y)
    (k : NonUnitalModuleHom S Z Z')
      (E : Left.TensorHom R S X Y Z hY ≃+ Left.CurriedHom R S X Y Z hY) (E' : Left.TensorHom R S X' Y' Z' hY' ≃+ Left.CurriedHom R S X' Y' Z' hY')
      (End : Left.TensorHom R S X Y Z hY ≃+ Left.RefinedHom R S X Y Z hY hR) (End' : Left.TensorHom R S X' Y' Z' hY' ≃+ Left.RefinedHom R S X' Y' Z' hY' hR),
      IsNondegenerate R X → IsNondegenerate R X' →
        Left.RefinedCanonical R S X Y Z hY hR E End →
        Left.RefinedCanonical R S X' Y' Z' hY' hR E' End' →
        Left.RefinedNaturality R S X Y Z hY hY' f g k hR End End') := rfl

example : NonUnitalTensorHomAdjunctionTheorem.{1, 0, 1, 0, 1, 0, 1, 0} =
    (Right.ExistenceTheorem.{1, 0, 1, 0, 1} ∧ Left.ExistenceTheorem.{1, 0, 1, 0, 1} ∧
     Right.NaturalityTheorem.{1, 0, 1, 0, 1, 0, 1, 0} ∧ Left.NaturalityTheorem.{1, 0, 1, 0, 1, 0, 1, 0} ∧
     Right.RefinedExistenceTheorem.{1, 0, 1, 0, 1} ∧ Left.RefinedExistenceTheorem.{1, 0, 1, 0, 1} ∧
     Right.RefinedNaturalityTheorem.{1, 0, 1, 0, 1, 0, 1, 0} ∧ Left.RefinedNaturalityTheorem.{1, 0, 1, 0, 1, 0, 1, 0}) := rfl

section RightCompeting
set_option linter.unusedVariables false
set_option linter.overlappingInstances false

variable (R : Type uR) (S : Type uS) (X : Type uX) (Y : Type uY) (Z : Type uZ)
  [r₁ : NonUnitalRing R] [r₂ : NonUnitalRing R]
  [s₁ : NonUnitalRing S] [s₂ : NonUnitalRing S]
  [x₁ : AddCommGroup X] [x₂ : AddCommGroup X]
  [y₁ : AddCommGroup Y] [y₂ : AddCommGroup Y]
  [z₁ : AddCommGroup Z] [z₂ : AddCommGroup Z]
  (rx : @NonUnitalModule Rᵐᵒᵖ X (@MulOpposite.instNonUnitalRing R r₁) x₁)
  (ry : @NonUnitalModule R Y r₁ y₁)
  (sy : @NonUnitalModule Sᵐᵒᵖ Y (@MulOpposite.instNonUnitalRing S s₁) y₁)
  (sz : @NonUnitalModule Sᵐᵒᵖ Z (@MulOpposite.instNonUnitalRing S s₁) z₁)
  (hY : @ActionsCommute R S Y r₁ s₁ y₁ ry sy)
  [rxOther : @NonUnitalModule Rᵐᵒᵖ X (@MulOpposite.instNonUnitalRing R r₁) x₁]
  [ryOther : @NonUnitalModule R Y r₁ y₁]
  [syOther : @NonUnitalModule Sᵐᵒᵖ Y (@MulOpposite.instNonUnitalRing S s₁) y₁]
  [szOther : @NonUnitalModule Sᵐᵒᵖ Z (@MulOpposite.instNonUnitalRing S s₁) z₁]
  [tensorGroupOther : AddCommGroup (@Tensor R X Y r₁ x₁ y₁ rx ry)]
  [tensorActionOther : @NonUnitalModule Sᵐᵒᵖ (@Tensor R X Y r₁ x₁ y₁ rx ry) (@MulOpposite.instNonUnitalRing S s₁) (@NonUnitalModuleTensor.addCommGroup R X Y r₁ x₁ y₁ rx ry)]
  [innerGroupOther : AddCommGroup (@NonUnitalModuleHom Sᵐᵒᵖ Y Z (@MulOpposite.instNonUnitalRing S s₁) y₁ z₁ sy sz)]
  [innerActionOther : @NonUnitalModule Rᵐᵒᵖ (@NonUnitalModuleHom Sᵐᵒᵖ Y Z (@MulOpposite.instNonUnitalRing S s₁) y₁ z₁ sy sz) (@MulOpposite.instNonUnitalRing R r₁) (@NonUnitalModuleHom.instAddCommGroup Sᵐᵒᵖ Y Z (@MulOpposite.instNonUnitalRing S s₁) y₁ z₁ sy sz)]
  [tensorHomGroupOther : AddCommGroup (@NonUnitalModuleHom Sᵐᵒᵖ (@Tensor R X Y r₁ x₁ y₁ rx ry) Z (@MulOpposite.instNonUnitalRing S s₁) (@NonUnitalModuleTensor.addCommGroup R X Y r₁ x₁ y₁ rx ry) z₁ (@rightModule R S r₁ s₁ X x₁ rx Y y₁ ry sy hY) sz)]
  [curriedHomGroupOther : AddCommGroup (@NonUnitalModuleHom Rᵐᵒᵖ X (@NonUnitalModuleHom Sᵐᵒᵖ Y Z (@MulOpposite.instNonUnitalRing S s₁) y₁ z₁ sy sz) (@MulOpposite.instNonUnitalRing R r₁) x₁ (@NonUnitalModuleHom.instAddCommGroup Sᵐᵒᵖ Y Z (@MulOpposite.instNonUnitalRing S s₁) y₁ z₁ sy sz) rx (@rightSourceAction R S Y Z r₁ s₁ y₁ z₁ ry sy sz hY))]

/- The raw carriers select the published quotient, groups and named actions. -/
example : @Right.TensorHom R S X Y Z r₁ s₁ x₁ y₁ z₁ rx ry sy sz hY = (@NonUnitalModuleHom Sᵐᵒᵖ (@Tensor R X Y r₁ x₁ y₁ rx ry) Z (@MulOpposite.instNonUnitalRing S s₁) (@NonUnitalModuleTensor.addCommGroup R X Y r₁ x₁ y₁ rx ry) z₁ (@rightModule R S r₁ s₁ X x₁ rx Y y₁ ry sy hY) sz) := rfl
example : @Right.CurriedHom R S X Y Z r₁ s₁ x₁ y₁ z₁ rx ry sy sz hY = (@NonUnitalModuleHom Rᵐᵒᵖ X (@NonUnitalModuleHom Sᵐᵒᵖ Y Z (@MulOpposite.instNonUnitalRing S s₁) y₁ z₁ sy sz) (@MulOpposite.instNonUnitalRing R r₁) x₁ (@NonUnitalModuleHom.instAddCommGroup Sᵐᵒᵖ Y Z (@MulOpposite.instNonUnitalRing S s₁) y₁ z₁ sy sz) rx (@rightSourceAction R S Y Z r₁ s₁ y₁ z₁ ry sy sz hY)) := rfl
example : @Right.tensorHomGroup R S X Y Z r₁ s₁ x₁ y₁ z₁ rx ry sy sz hY = (@NonUnitalModuleHom.instAddCommGroup Sᵐᵒᵖ (@Tensor R X Y r₁ x₁ y₁ rx ry) Z (@MulOpposite.instNonUnitalRing S s₁) (@NonUnitalModuleTensor.addCommGroup R X Y r₁ x₁ y₁ rx ry) z₁ (@rightModule R S r₁ s₁ X x₁ rx Y y₁ ry sy hY) sz) := rfl
example : @Right.curriedHomGroup R S X Y Z r₁ s₁ x₁ y₁ z₁ rx ry sy sz hY = (@NonUnitalModuleHom.instAddCommGroup Rᵐᵒᵖ X (@NonUnitalModuleHom Sᵐᵒᵖ Y Z (@MulOpposite.instNonUnitalRing S s₁) y₁ z₁ sy sz) (@MulOpposite.instNonUnitalRing R r₁) x₁ (@NonUnitalModuleHom.instAddCommGroup Sᵐᵒᵖ Y Z (@MulOpposite.instNonUnitalRing S s₁) y₁ z₁ sy sz) rx (@rightSourceAction R S Y Z r₁ s₁ y₁ z₁ ry sy sz hY)) := rfl

example (hR : @IsIdempotented R r₁) :
    @Right.HomPart R S Y Z r₁ s₁ y₁ z₁ ry sy sz hY hR =
      @nondegeneratePart Rᵐᵒᵖ (@MulOpposite.instNonUnitalRing R r₁) (@IsIdempotented.op R r₁ hR) (@NonUnitalModuleHom Sᵐᵒᵖ Y Z (@MulOpposite.instNonUnitalRing S s₁) y₁ z₁ sy sz) (@NonUnitalModuleHom.instAddCommGroup Sᵐᵒᵖ Y Z (@MulOpposite.instNonUnitalRing S s₁) y₁ z₁ sy sz) (@rightSourceAction R S Y Z r₁ s₁ y₁ z₁ ry sy sz hY) := rfl

example (hR : @IsIdempotented R r₁) :
    @Right.RefinedHom R S X Y Z r₁ s₁ x₁ y₁ z₁ rx ry sy sz hY hR =
      (letI := r₁
       letI := s₁
       letI := x₁
       letI := y₁
       letI := z₁
       letI := rx
       letI := ry
       letI := sy
       letI := sz
       NonUnitalModuleHom Rᵐᵒᵖ X (@Right.HomPart R S Y Z r₁ s₁ y₁ z₁ ry sy sz hY hR)) := rfl

example (hR : @IsIdempotented R r₁) :
    @Right.refinedHomGroup R S X Y Z r₁ s₁ x₁ y₁ z₁ rx ry sy sz hY hR =
      (letI := r₁
       letI := s₁
       letI := x₁
       letI := y₁
       letI := z₁
       letI := rx
       letI := ry
       letI := sy
       letI := sz
       (NonUnitalModuleHom.instAddCommGroup :
         AddCommGroup (NonUnitalModuleHom Rᵐᵒᵖ X (@Right.HomPart R S Y Z r₁ s₁ y₁ z₁ ry sy sz hY hR)))) := rfl

example :
    @Right.ExistsCanonical R S X Y Z r₁ s₁ x₁ y₁ z₁ rx ry sy sz hY =
      (letI := r₁
       letI := s₁
       letI := x₁
       letI := y₁
       letI := z₁
       letI := rx
       letI := ry
       letI := sy
       letI := sz
       letI := @NonUnitalModuleTensor.addCommGroup R X Y r₁ x₁ y₁ rx ry
       letI := @NonUnitalModuleHom.instAddCommGroup Sᵐᵒᵖ Y Z (@MulOpposite.instNonUnitalRing S s₁) y₁ z₁ sy sz
       letI := @rightModule R S r₁ s₁ X x₁ rx Y y₁ ry sy hY
       letI := @rightSourceAction R S Y Z r₁ s₁ y₁ z₁ ry sy sz hY
       ∃ E : NonUnitalModuleHom Sᵐᵒᵖ (@Tensor R X Y r₁ x₁ y₁ rx ry) Z ≃+
           NonUnitalModuleHom Rᵐᵒᵖ X (@NonUnitalModuleHom Sᵐᵒᵖ Y Z (@MulOpposite.instNonUnitalRing S s₁) y₁ z₁ sy sz),
         @Right.Canonical R S X Y Z r₁ s₁ x₁ y₁ z₁ rx ry sy sz hY E) := rfl

example (hR : @IsIdempotented R r₁) :
    @Right.inclusionMap R S X Y Z r₁ s₁ x₁ y₁ z₁ rx ry sy sz hY hR =
      (letI := r₁
       letI := s₁
       letI := x₁
       letI := y₁
       letI := z₁
       letI := rx
       letI := ry
       letI := sy
       letI := sz
       letI := @NonUnitalModuleHom.instAddCommGroup Sᵐᵒᵖ Y Z (@MulOpposite.instNonUnitalRing S s₁) y₁ z₁ sy sz
       letI := @rightSourceAction R S Y Z r₁ s₁ y₁ z₁ ry sy sz hY
       postcomposeAddHom (@Right.HomPart R S Y Z r₁ s₁ y₁ z₁ ry sy sz hY hR).subtype) := rfl

end RightCompeting

section LeftCompeting
set_option linter.unusedVariables false
set_option linter.overlappingInstances false

variable (R : Type uR) (S : Type uS) (X : Type uX) (Y : Type uY) (Z : Type uZ)
  [r₁ : NonUnitalRing R] [r₂ : NonUnitalRing R]
  [s₁ : NonUnitalRing S] [s₂ : NonUnitalRing S]
  [x₁ : AddCommGroup X] [x₂ : AddCommGroup X]
  [y₁ : AddCommGroup Y] [y₂ : AddCommGroup Y]
  [z₁ : AddCommGroup Z] [z₂ : AddCommGroup Z]
  (rx : @NonUnitalModule R X r₁ x₁)
  (sy : @NonUnitalModule S Y s₁ y₁)
  (ry : @NonUnitalModule Rᵐᵒᵖ Y (@MulOpposite.instNonUnitalRing R r₁) y₁)
  (sz : @NonUnitalModule S Z s₁ z₁)
  (hY : @ActionsCommute S R Y s₁ r₁ y₁ sy ry)
  [rxOther : @NonUnitalModule R X r₁ x₁]
  [ryOther : @NonUnitalModule Rᵐᵒᵖ Y (@MulOpposite.instNonUnitalRing R r₁) y₁]
  [syOther : @NonUnitalModule S Y s₁ y₁]
  [szOther : @NonUnitalModule S Z s₁ z₁]
  [tensorGroupOther : AddCommGroup (@Tensor R Y X r₁ y₁ x₁ ry rx)]
  [tensorActionOther : @NonUnitalModule S (@Tensor R Y X r₁ y₁ x₁ ry rx) s₁ (@NonUnitalModuleTensor.addCommGroup R Y X r₁ y₁ x₁ ry rx)]
  [innerGroupOther : AddCommGroup (@NonUnitalModuleHom S Y Z s₁ y₁ z₁ sy sz)]
  [innerActionOther : @NonUnitalModule R (@NonUnitalModuleHom S Y Z s₁ y₁ z₁ sy sz) r₁ (@NonUnitalModuleHom.instAddCommGroup S Y Z s₁ y₁ z₁ sy sz)]
  [tensorHomGroupOther : AddCommGroup (@NonUnitalModuleHom S (@Tensor R Y X r₁ y₁ x₁ ry rx) Z s₁ (@NonUnitalModuleTensor.addCommGroup R Y X r₁ y₁ x₁ ry rx) z₁ (@leftModule S R s₁ r₁ Y y₁ sy ry hY X x₁ rx) sz)]
  [curriedHomGroupOther : AddCommGroup (@NonUnitalModuleHom R X (@NonUnitalModuleHom S Y Z s₁ y₁ z₁ sy sz) r₁ x₁ (@NonUnitalModuleHom.instAddCommGroup S Y Z s₁ y₁ z₁ sy sz) rx (@sourceAction S R Y Z s₁ r₁ y₁ z₁ sy ry sz hY))]

/- The raw carriers select the published quotient, groups and named actions. -/
example : @Left.TensorHom R S X Y Z r₁ s₁ x₁ y₁ z₁ rx sy ry sz hY = (@NonUnitalModuleHom S (@Tensor R Y X r₁ y₁ x₁ ry rx) Z s₁ (@NonUnitalModuleTensor.addCommGroup R Y X r₁ y₁ x₁ ry rx) z₁ (@leftModule S R s₁ r₁ Y y₁ sy ry hY X x₁ rx) sz) := rfl
example : @Left.CurriedHom R S X Y Z r₁ s₁ x₁ y₁ z₁ rx sy ry sz hY = (@NonUnitalModuleHom R X (@NonUnitalModuleHom S Y Z s₁ y₁ z₁ sy sz) r₁ x₁ (@NonUnitalModuleHom.instAddCommGroup S Y Z s₁ y₁ z₁ sy sz) rx (@sourceAction S R Y Z s₁ r₁ y₁ z₁ sy ry sz hY)) := rfl
example : @Left.tensorHomGroup R S X Y Z r₁ s₁ x₁ y₁ z₁ rx sy ry sz hY = (@NonUnitalModuleHom.instAddCommGroup S (@Tensor R Y X r₁ y₁ x₁ ry rx) Z s₁ (@NonUnitalModuleTensor.addCommGroup R Y X r₁ y₁ x₁ ry rx) z₁ (@leftModule S R s₁ r₁ Y y₁ sy ry hY X x₁ rx) sz) := rfl
example : @Left.curriedHomGroup R S X Y Z r₁ s₁ x₁ y₁ z₁ rx sy ry sz hY = (@NonUnitalModuleHom.instAddCommGroup R X (@NonUnitalModuleHom S Y Z s₁ y₁ z₁ sy sz) r₁ x₁ (@NonUnitalModuleHom.instAddCommGroup S Y Z s₁ y₁ z₁ sy sz) rx (@sourceAction S R Y Z s₁ r₁ y₁ z₁ sy ry sz hY)) := rfl

example (hR : @IsIdempotented R r₁) :
    @Left.HomPart R S Y Z r₁ s₁ y₁ z₁ sy ry sz hY hR =
      @nondegeneratePart R r₁ (hR) (@NonUnitalModuleHom S Y Z s₁ y₁ z₁ sy sz) (@NonUnitalModuleHom.instAddCommGroup S Y Z s₁ y₁ z₁ sy sz) (@sourceAction S R Y Z s₁ r₁ y₁ z₁ sy ry sz hY) := rfl

example (hR : @IsIdempotented R r₁) :
    @Left.RefinedHom R S X Y Z r₁ s₁ x₁ y₁ z₁ rx sy ry sz hY hR =
      (letI := r₁
       letI := s₁
       letI := x₁
       letI := y₁
       letI := z₁
       letI := rx
       letI := ry
       letI := sy
       letI := sz
       NonUnitalModuleHom R X (@Left.HomPart R S Y Z r₁ s₁ y₁ z₁ sy ry sz hY hR)) := rfl

example (hR : @IsIdempotented R r₁) :
    @Left.refinedHomGroup R S X Y Z r₁ s₁ x₁ y₁ z₁ rx sy ry sz hY hR =
      (letI := r₁
       letI := s₁
       letI := x₁
       letI := y₁
       letI := z₁
       letI := rx
       letI := ry
       letI := sy
       letI := sz
       (NonUnitalModuleHom.instAddCommGroup :
         AddCommGroup (NonUnitalModuleHom R X (@Left.HomPart R S Y Z r₁ s₁ y₁ z₁ sy ry sz hY hR)))) := rfl

example :
    @Left.ExistsCanonical R S X Y Z r₁ s₁ x₁ y₁ z₁ rx sy ry sz hY =
      (letI := r₁
       letI := s₁
       letI := x₁
       letI := y₁
       letI := z₁
       letI := rx
       letI := ry
       letI := sy
       letI := sz
       letI := @NonUnitalModuleTensor.addCommGroup R Y X r₁ y₁ x₁ ry rx
       letI := @NonUnitalModuleHom.instAddCommGroup S Y Z s₁ y₁ z₁ sy sz
       letI := @leftModule S R s₁ r₁ Y y₁ sy ry hY X x₁ rx
       letI := @sourceAction S R Y Z s₁ r₁ y₁ z₁ sy ry sz hY
       ∃ E : NonUnitalModuleHom S (@Tensor R Y X r₁ y₁ x₁ ry rx) Z ≃+
           NonUnitalModuleHom R X (@NonUnitalModuleHom S Y Z s₁ y₁ z₁ sy sz),
         @Left.Canonical R S X Y Z r₁ s₁ x₁ y₁ z₁ rx sy ry sz hY E) := rfl

example (hR : @IsIdempotented R r₁) :
    @Left.inclusionMap R S X Y Z r₁ s₁ x₁ y₁ z₁ rx sy ry sz hY hR =
      (letI := r₁
       letI := s₁
       letI := x₁
       letI := y₁
       letI := z₁
       letI := rx
       letI := ry
       letI := sy
       letI := sz
       letI := @NonUnitalModuleHom.instAddCommGroup S Y Z s₁ y₁ z₁ sy sz
       letI := @sourceAction S R Y Z s₁ r₁ y₁ z₁ sy ry sz hY
       postcomposeAddHom (@Left.HomPart R S Y Z r₁ s₁ y₁ z₁ sy ry sz hY hR).subtype) := rfl

end LeftCompeting

section ZeroOriginalActions

local instance zeroIntegerAction : NonUnitalModule ℤ ℤ := NonUnitalModule.zero
local instance zeroIntegerRightAction : NonUnitalModule ℤᵐᵒᵖ ℤ := NonUnitalModule.zero

private theorem zeroIntegerCommute : ActionsCommute ℤ ℤ ℤ := by
  intro r s y
  rfl

/- These specialize the closed targets; they do not prove the targets. -/
example (h : Right.ExistenceTheorem.{0, 0, 0, 0, 0}) :
    Right.ExistsCanonical ℤ ℤ ℤ ℤ ℤ zeroIntegerCommute :=
  h ℤ ℤ ℤ ℤ ℤ zeroIntegerCommute

example (h : Left.ExistenceTheorem.{0, 0, 0, 0, 0}) :
    Left.ExistsCanonical ℤ ℤ ℤ ℤ ℤ zeroIntegerCommute :=
  h ℤ ℤ ℤ ℤ ℤ zeroIntegerCommute

private def multiplication : ℤ →+ ℤ →+ ℤ where
  toFun x :=
    { toFun := fun y => x * y
      map_zero' := mul_zero x
      map_add' := mul_add x }
  map_zero' := AddMonoidHom.ext zero_mul
  map_add' x x' := AddMonoidHom.ext (add_mul x x')

private theorem multiplication_balanced :
    NonUnitalModuleTensor.IsBalanced ℤ multiplication := by
  intro r x y
  change (0 : ℤ) * y = x * 0
  simp

/-- The original quotient remains nonzero under zero original actions. -/
example : tmul ℤ ℤ ℤ 1 1 ≠ 0 := by
  intro h
  have bad := congrArg (lift ℤ multiplication multiplication_balanced) h
  rw [NonUnitalModuleTensor.lift_tmul, map_zero] at bad
  change (1 : ℤ) = 0 at bad
  exact one_ne_zero bad

/-- The actual inner Hom in the left-handed target is nonzero. -/
example : NonUnitalModuleHom.id ℤ ℤ ≠ 0 := by
  intro h
  have bad := congrArg (fun f : NonUnitalModuleHom ℤ ℤ ℤ => f 1) h
  change (1 : ℤ) = 0 at bad
  exact one_ne_zero bad

/-- The actual inner Hom in the right-handed target is nonzero. -/
example : NonUnitalModuleHom.id ℤᵐᵒᵖ ℤ ≠ 0 := by
  intro h
  have bad := congrArg (fun f : NonUnitalModuleHom ℤᵐᵒᵖ ℤ ℤ => f 1) h
  change (1 : ℤ) = 0 at bad
  exact one_ne_zero bad

example : ¬ IsUnitalModule ℤ ℤ := by
  intro h
  have bad := h 1
  change (0 : ℤ) = 1 at bad
  exact zero_ne_one bad

example : ¬ IsUnitalModule ℤᵐᵒᵖ ℤ := by
  intro h
  have bad := h 1
  change (0 : ℤ) = 1 at bad
  exact zero_ne_one bad

example : ¬ IsNondegenerate ℤ ℤ := by
  intro h
  obtain ⟨e, he⟩ := h 1
  change (0 : ℤ) = 1 at he
  exact zero_ne_one he

example : ¬ IsNondegenerate ℤᵐᵒᵖ ℤ := by
  intro h
  obtain ⟨e, he⟩ := h 1
  change (0 : ℤ) = 1 at he
  exact zero_ne_one he

end ZeroOriginalActions

section SubsingletonCarriers

local instance : NonUnitalModule ℤ PUnit.{1} := NonUnitalModule.zero
local instance : NonUnitalModule ℤᵐᵒᵖ PUnit.{1} := NonUnitalModule.zero

private theorem subsingletonCommute : ActionsCommute ℤ ℤ PUnit.{1} :=
  fun _ _ _ => Subsingleton.elim _ _

example (h : Right.ExistenceTheorem.{0, 0, 0, 0, 0}) :
    Right.ExistsCanonical ℤ ℤ PUnit.{1} PUnit.{1} PUnit.{1} subsingletonCommute :=
  h ℤ ℤ PUnit.{1} PUnit.{1} PUnit.{1} subsingletonCommute

example (h : Left.ExistenceTheorem.{0, 0, 0, 0, 0}) :
    Left.ExistsCanonical ℤ ℤ PUnit.{1} PUnit.{1} PUnit.{1} subsingletonCommute :=
  h ℤ ℤ PUnit.{1} PUnit.{1} PUnit.{1} subsingletonCommute

end SubsingletonCarriers

section RegularIntegerActions

local instance : NonUnitalModule ℤ ℤ := NonUnitalModule.regular ℤ
local instance : NonUnitalModule ℤᵐᵒᵖ ℤ := NonUnitalModule.rightRegular ℤ

example (h : Right.ExistenceTheorem.{0, 0, 0, 0, 0}) :
    Right.ExistsCanonical ℤ ℤ ℤ ℤ ℤ (NonUnitalModule.regular_actionsCommute ℤ) :=
  h ℤ ℤ ℤ ℤ ℤ (NonUnitalModule.regular_actionsCommute ℤ)

example (h : Left.ExistenceTheorem.{0, 0, 0, 0, 0}) :
    Left.ExistsCanonical ℤ ℤ ℤ ℤ ℤ (NonUnitalModule.regular_actionsCommute ℤ) :=
  h ℤ ℤ ℤ ℤ ℤ (NonUnitalModule.regular_actionsCommute ℤ)

end RegularIntegerActions

end Langlands.Algebra.NonUnitalTensorHomAdjunctionChecks
