import Langlands.Algebra.NonUnitalBimoduleHomActions

set_option autoImplicit false
-- Interface abbreviations are types whose sort intentionally takes a maximum.
set_option linter.checkUnivs false

open MulOpposite

namespace Langlands.Algebra.NonUnitalBimoduleHomActions

universe uS uR uT uY uZ

/-! These are complete unapplied types, including the specified action choices. -/

private abbrev SourceActionInterface :=
  {S : Type uS} → {R : Type uR} → {Y : Type uY} → {Z : Type uZ} →
  [s : NonUnitalRing S] → [r : NonUnitalRing R] →
  [y : AddCommGroup Y] → [z : AddCommGroup Z] →
  [sy : NonUnitalModule S Y] → [ry : NonUnitalModule Rᵐᵒᵖ Y] →
  [sz : NonUnitalModule S Z] →
  (hY : @ActionsCommute S R Y s r y sy ry) →
  NonUnitalModule R (@NonUnitalModuleHom S Y Z s y z sy sz)

example : SourceActionInterface.{uS, uR, uY, uZ} := @sourceAction.{uS, uR, uY, uZ}
example : SourceActionInterface.{0, 1, 0, 1} := @sourceAction.{0, 1, 0, 1}
example : SourceActionInterface.{1, 0, 1, 0} := @sourceAction.{1, 0, 1, 0}

private abbrev TargetActionInterface :=
  {S : Type uS} → {T : Type uT} → {Y : Type uY} → {Z : Type uZ} →
  [s : NonUnitalRing S] → [t : NonUnitalRing T] →
  [y : AddCommGroup Y] → [z : AddCommGroup Z] →
  [sy : NonUnitalModule S Y] → [sz : NonUnitalModule S Z] →
  [tz : NonUnitalModule Tᵐᵒᵖ Z] →
  (hZ : @ActionsCommute S T Z s t z sz tz) →
  NonUnitalModule Tᵐᵒᵖ (@NonUnitalModuleHom S Y Z s y z sy sz)

example : TargetActionInterface.{uS, uT, uY, uZ} := @targetAction.{uS, uT, uY, uZ}
example : TargetActionInterface.{0, 1, 1, 0} := @targetAction.{0, 1, 1, 0}
example : TargetActionInterface.{1, 0, 0, 1} := @targetAction.{1, 0, 0, 1}

private abbrev CommuteInterface :=
  {S : Type uS} → {R : Type uR} → {T : Type uT} →
  {Y : Type uY} → {Z : Type uZ} →
  [s : NonUnitalRing S] → [r : NonUnitalRing R] → [t : NonUnitalRing T] →
  [y : AddCommGroup Y] → [z : AddCommGroup Z] →
  [sy : NonUnitalModule S Y] → [ry : NonUnitalModule Rᵐᵒᵖ Y] →
  [sz : NonUnitalModule S Z] → [tz : NonUnitalModule Tᵐᵒᵖ Z] →
  (hY : @ActionsCommute S R Y s r y sy ry) →
  (hZ : @ActionsCommute S T Z s t z sz tz) →
  @ActionsCommute R T (@NonUnitalModuleHom S Y Z s y z sy sz) r t _
    (@sourceAction S R Y Z s r y z sy ry sz hY)
    (@targetAction S T Y Z s t y z sy sz tz hZ)

example : CommuteInterface.{uS, uR, uT, uY, uZ} := @actionsCommute.{uS, uR, uT, uY, uZ}
example : CommuteInterface.{0, 1, 0, 1, 0} := @actionsCommute.{0, 1, 0, 1, 0}
example : CommuteInterface.{1, 0, 1, 0, 1} := @actionsCommute.{1, 0, 1, 0, 1}

private abbrev HomInterface :=
  {S : Type uS} → {R : Type uR} → {T : Type uT} →
  {Y : Type uY} → {Z : Type uZ} →
  [s : NonUnitalRing S] → [r : NonUnitalRing R] → [t : NonUnitalRing T] →
  [y : AddCommGroup Y] → [z : AddCommGroup Z] →
  [sy : NonUnitalModule S Y] → [ry : NonUnitalModule Rᵐᵒᵖ Y] →
  [sz : NonUnitalModule S Z] → [tz : NonUnitalModule Tᵐᵒᵖ Z] →
  (hY : @ActionsCommute S R Y s r y sy ry) →
  (hZ : @ActionsCommute S T Z s t z sz tz) →
  @NonUnitalBimoduleCat.{uR, uT, max uY uZ} R T r t

example : HomInterface.{uS, uR, uT, uY, uZ} := @hom.{uS, uR, uT, uY, uZ}
example : HomInterface.{0, 1, 0, 1, 0} := @hom.{0, 1, 0, 1, 0}
example : HomInterface.{1, 0, 1, 0, 1} := @hom.{1, 0, 1, 0, 1}

private abbrev RightSourceActionInterface :=
  {R : Type uR} → {S : Type uS} → {Y : Type uY} → {Z : Type uZ} →
  [r : NonUnitalRing R] → [s : NonUnitalRing S] →
  [y : AddCommGroup Y] → [z : AddCommGroup Z] →
  [ry : NonUnitalModule R Y] → [sy : NonUnitalModule Sᵐᵒᵖ Y] →
  [sz : NonUnitalModule Sᵐᵒᵖ Z] →
  (hY : @ActionsCommute R S Y r s y ry sy) →
  NonUnitalModule Rᵐᵒᵖ (@NonUnitalModuleHom Sᵐᵒᵖ Y Z _ y z sy sz)

example : RightSourceActionInterface.{uR, uS, uY, uZ} :=
  @rightSourceAction.{uR, uS, uY, uZ}
example : RightSourceActionInterface.{0, 1, 0, 1} := @rightSourceAction.{0, 1, 0, 1}
example : RightSourceActionInterface.{1, 0, 1, 0} := @rightSourceAction.{1, 0, 1, 0}

private abbrev RegularActionInterface :=
  {A : Type uS} → [a : NonUnitalRing A] →
  {M : Type uZ} → [m : AddCommGroup M] → [hM : NonUnitalModule A M] →
  NonUnitalModule A (@NonUnitalModuleHom A A M a _ m (NonUnitalModule.regular A) hM)

example : RegularActionInterface.{uS, uZ} := @regularSourceAction.{uS, uZ}
example : RegularActionInterface.{0, 1} := @regularSourceAction.{0, 1}
example : RegularActionInterface.{1, 0} := @regularSourceAction.{1, 0}

private abbrev FromRegularInterface :=
  {A : Type uS} → [a : NonUnitalRing A] →
  {M : Type uZ} → [m : AddCommGroup M] → [hM : NonUnitalModule A M] →
  @NonUnitalModuleHom A (RegularModuleHom A M)
    (@NonUnitalModuleHom A A M a _ m (NonUnitalModule.regular A) hM) a _ _
    (@RegularModuleHom.instNonUnitalModule A a M m hM)
    (@regularSourceAction A a M m hM)

example : FromRegularInterface.{uS, uZ} := @fromRegular.{uS, uZ}
example : FromRegularInterface.{0, 1} := @fromRegular.{0, 1}
example : FromRegularInterface.{1, 0} := @fromRegular.{1, 0}

private abbrev ToRegularInterface :=
  {A : Type uS} → [a : NonUnitalRing A] →
  {M : Type uZ} → [m : AddCommGroup M] → [hM : NonUnitalModule A M] →
  @NonUnitalModuleHom A
    (@NonUnitalModuleHom A A M a _ m (NonUnitalModule.regular A) hM)
    (RegularModuleHom A M) a _ _ (@regularSourceAction A a M m hM)
    (@RegularModuleHom.instNonUnitalModule A a M m hM)

example : ToRegularInterface.{uS, uZ} := @toRegular.{uS, uZ}
example : ToRegularInterface.{0, 1} := @toRegular.{0, 1}
example : ToRegularInterface.{1, 0} := @toRegular.{1, 0}

private abbrev SourceEndInterface :=
  {S : Type uS} → {R : Type uR} → {Y : Type uY} → {Z : Type uZ} →
  [s : NonUnitalRing S] → [r : NonUnitalRing R] →
  [y : AddCommGroup Y] → [z : AddCommGroup Z] →
  [sy : NonUnitalModule S Y] → [ry : NonUnitalModule Rᵐᵒᵖ Y] →
  [sz : NonUnitalModule S Z] →
  (hY : @ActionsCommute S R Y s r y sy ry) → (a : R) →
  NonUnitalModule.toEndHom (@sourceAction S R Y Z s r y z sy ry sz hY) a =
    precomposeAddHom (hY.rightActionHom (op a))

example : SourceEndInterface.{uS, uR, uY, uZ} := @sourceAction_toEndHom.{uS, uR, uY, uZ}
example : SourceEndInterface.{0, 1, 0, 1} := @sourceAction_toEndHom.{0, 1, 0, 1}
example : SourceEndInterface.{1, 0, 1, 0} := @sourceAction_toEndHom.{1, 0, 1, 0}

private abbrev TargetEndInterface :=
  {S : Type uS} → {T : Type uT} → {Y : Type uY} → {Z : Type uZ} →
  [s : NonUnitalRing S] → [t : NonUnitalRing T] →
  [y : AddCommGroup Y] → [z : AddCommGroup Z] →
  [sy : NonUnitalModule S Y] → [sz : NonUnitalModule S Z] →
  [tz : NonUnitalModule Tᵐᵒᵖ Z] →
  (hZ : @ActionsCommute S T Z s t z sz tz) → (b : Tᵐᵒᵖ) →
  NonUnitalModule.toEndHom (@targetAction S T Y Z s t y z sy sz tz hZ) b =
    postcomposeAddHom (hZ.rightActionHom b)

example : TargetEndInterface.{uS, uT, uY, uZ} := @targetAction_toEndHom.{uS, uT, uY, uZ}
example : TargetEndInterface.{0, 1, 1, 0} := @targetAction_toEndHom.{0, 1, 1, 0}
example : TargetEndInterface.{1, 0, 0, 1} := @targetAction_toEndHom.{1, 0, 0, 1}

private abbrev RightSourceEndInterface :=
  {R : Type uR} → {S : Type uS} → {Y : Type uY} → {Z : Type uZ} →
  [r : NonUnitalRing R] → [s : NonUnitalRing S] →
  [y : AddCommGroup Y] → [z : AddCommGroup Z] →
  [ry : NonUnitalModule R Y] → [sy : NonUnitalModule Sᵐᵒᵖ Y] →
  [sz : NonUnitalModule Sᵐᵒᵖ Z] →
  (hY : @ActionsCommute R S Y r s y ry sy) → (a : Rᵐᵒᵖ) →
  NonUnitalModule.toEndHom (@rightSourceAction R S Y Z r s y z ry sy sz hY) a =
    precomposeAddHom (hY.leftActionHom a.unop)

example : RightSourceEndInterface.{uR, uS, uY, uZ} :=
  @rightSourceAction_toEndHom.{uR, uS, uY, uZ}
example : RightSourceEndInterface.{0, 1, 0, 1} := @rightSourceAction_toEndHom.{0, 1, 0, 1}
example : RightSourceEndInterface.{1, 0, 1, 0} := @rightSourceAction_toEndHom.{1, 0, 1, 0}

private abbrev RegularCompatInterface :=
  {A : Type uS} → [a : NonUnitalRing A] →
  {M : Type uZ} → [m : AddCommGroup M] → [hM : NonUnitalModule A M] → (b : A) →
  (NonUnitalModule.toEndHom (@regularSourceAction A a M m hM) b).comp
    (@RegularModuleHom.equivNonUnitalModuleHom A a M m hM).toAddMonoidHom =
  (@RegularModuleHom.equivNonUnitalModuleHom A a M m hM).toAddMonoidHom.comp
    (NonUnitalModule.toEndHom (@RegularModuleHom.instNonUnitalModule A a M m hM) b)

example : RegularCompatInterface.{uS, uZ} := @regularSourceAction_compat.{uS, uZ}
example : RegularCompatInterface.{0, 1} := @regularSourceAction_compat.{0, 1}
example : RegularCompatInterface.{1, 0} := @regularSourceAction_compat.{1, 0}

section Competing

variable {S : Type uS} {R : Type uR} {T : Type uT} {Y : Type uY} {Z : Type uZ}
  [s₁ : NonUnitalRing S] [s₂ : NonUnitalRing S]
  [r₁ : NonUnitalRing R] [r₂ : NonUnitalRing R]
  [t₁ : NonUnitalRing T] [t₂ : NonUnitalRing T]
  [y₁ : AddCommGroup Y] [y₂ : AddCommGroup Y]
  [z₁ : AddCommGroup Z] [z₂ : AddCommGroup Z]
  (sy : @NonUnitalModule S Y s₁ y₁) (ry : @NonUnitalModule Rᵐᵒᵖ Y (@MulOpposite.instNonUnitalRing R r₁) y₁)
  (sz : @NonUnitalModule S Z s₁ z₁) (tz : @NonUnitalModule Tᵐᵒᵖ Z (@MulOpposite.instNonUnitalRing T t₁) z₁)
  (hY : @ActionsCommute S R Y s₁ r₁ y₁ sy ry)
  (hZ : @ActionsCommute S T Z s₁ t₁ z₁ sz tz)
  [syOther : @NonUnitalModule S Y s₁ y₁]
  [ryOther : @NonUnitalModule Rᵐᵒᵖ Y (@MulOpposite.instNonUnitalRing R r₁) y₁]
  [szOther : @NonUnitalModule S Z s₁ z₁]
  [tzOther : @NonUnitalModule Tᵐᵒᵖ Z (@MulOpposite.instNonUnitalRing T t₁) z₁]
  [homLeftOther : @NonUnitalModule R
    (@NonUnitalModuleHom S Y Z s₁ y₁ z₁ sy sz) r₁
    (@NonUnitalModuleHom.instAddCommGroup S Y Z s₁ y₁ z₁ sy sz)]
  [homRightOther : @NonUnitalModule Tᵐᵒᵖ
    (@NonUnitalModuleHom S Y Z s₁ y₁ z₁ sy sz) (@MulOpposite.instNonUnitalRing T t₁)
    (@NonUnitalModuleHom.instAddCommGroup S Y Z s₁ y₁ z₁ sy sz)]

set_option linter.overlappingInstances false in
/-- Explicit inputs preserve the original group and both named residual actions. -/
example :
    let B := @hom S R T Y Z s₁ r₁ t₁ y₁ z₁ sy ry sz tz hY hZ
    @NonUnitalBimoduleCat.carrier R T r₁ t₁ B =
      @NonUnitalModuleHom S Y Z s₁ y₁ z₁ sy sz ∧
    @NonUnitalBimoduleCat.isAddCommGroup R T r₁ t₁ B =
      @NonUnitalModuleHom.instAddCommGroup S Y Z s₁ y₁ z₁ sy sz ∧
    @NonUnitalBimoduleCat.isLeftModule R T r₁ t₁ B =
      @sourceAction S R Y Z s₁ r₁ y₁ z₁ sy ry sz hY ∧
    @NonUnitalBimoduleCat.isRightModule R T r₁ t₁ B =
      @targetAction S T Y Z s₁ t₁ y₁ z₁ sy sz tz hZ :=
  ⟨rfl, rfl, rfl, rfl⟩

end Competing

section RegularCompeting

variable {A : Type uS} {M : Type uZ}
  [a₁ : NonUnitalRing A] [a₂ : NonUnitalRing A]
  [m₁ : AddCommGroup M] [m₂ : AddCommGroup M]
  (hM : @NonUnitalModule A M a₁ m₁)
  [hOther : @NonUnitalModule A M a₁ m₁]
  [homOther : @NonUnitalModule A
    (@NonUnitalModuleHom A A M a₁
      (@NonUnitalNonAssocRing.toAddCommGroup A (@NonUnitalRing.toNonUnitalNonAssocRing A a₁)) m₁ (@NonUnitalModule.regular A a₁) hM) a₁
    (@NonUnitalModuleHom.instAddCommGroup A A M a₁
      (@NonUnitalNonAssocRing.toAddCommGroup A (@NonUnitalRing.toNonUnitalNonAssocRing A a₁)) m₁
      (@NonUnitalModule.regular A a₁) hM)]

set_option linter.overlappingInstances false in
example :
    @NonUnitalModuleHom A (@RegularModuleHom A M a₁ m₁ hM)
      (@NonUnitalModuleHom A A M a₁
      (@NonUnitalNonAssocRing.toAddCommGroup A (@NonUnitalRing.toNonUnitalNonAssocRing A a₁)) m₁ (@NonUnitalModule.regular A a₁) hM) a₁ _ _
      (@RegularModuleHom.instNonUnitalModule A a₁ M m₁ hM)
      (@regularSourceAction A a₁ M m₁ hM) :=
  @fromRegular A a₁ M m₁ hM

set_option linter.overlappingInstances false in
example :
    @NonUnitalModuleHom A
      (@NonUnitalModuleHom A A M a₁
      (@NonUnitalNonAssocRing.toAddCommGroup A (@NonUnitalRing.toNonUnitalNonAssocRing A a₁)) m₁ (@NonUnitalModule.regular A a₁) hM)
      (@RegularModuleHom A M a₁ m₁ hM) a₁ _ _
      (@regularSourceAction A a₁ M m₁ hM)
      (@RegularModuleHom.instNonUnitalModule A a₁ M m₁ hM) :=
  @toRegular A a₁ M m₁ hM

end RegularCompeting

section Subsingleton

variable {S : Type uS} {R : Type uR} {T : Type uT} {Y : Type uY} {Z : Type uZ}
  [NonUnitalRing S] [NonUnitalRing R] [NonUnitalRing T]
  [AddCommGroup Y] [AddCommGroup Z]
  [NonUnitalModule S Y] [NonUnitalModule Rᵐᵒᵖ Y]
  [NonUnitalModule S Z] [NonUnitalModule Tᵐᵒᵖ Z]
  (hY : ActionsCommute S R Y) (hZ : ActionsCommute S T Z)

example [Subsingleton Z] : Subsingleton (hom hY hZ) := hom_subsingleton
example [Subsingleton Y] : Subsingleton (hom hY hZ) := hom_subsingleton_of_source

end Subsingleton

section IntegerZero

variable (S : Type uS) (R : Type uR) (T : Type uT)
  [NonUnitalRing S] [Ring R] [Ring T]

local instance intSource : NonUnitalModule S ℤ := NonUnitalModule.zero
local instance intSourceRight : NonUnitalModule Rᵐᵒᵖ ℤ := NonUnitalModule.zero
local instance intTargetRight : NonUnitalModule Tᵐᵒᵖ ℤ := NonUnitalModule.zero

/-- Even with unital residual rings, zero actions act on a nonzero actual Hom. -/
example :
    let B := hom
      (actionsCommute_zero_left (A := S) (B := R) (M := ℤ))
      (actionsCommute_zero_left (A := S) (B := T) (M := ℤ))
    let i : B := NonUnitalModuleHom.id S ℤ
    i ≠ 0 ∧
      (∀ r : R, NonUnitalModule.toEndHom B.isLeftModule r = 0) ∧
      (∀ t : Tᵐᵒᵖ, NonUnitalModule.toEndHom B.isRightModule t = 0) := by
  refine ⟨?_, ?_, ?_⟩
  · intro e
    have bad : (1 : ℤ) = 0 := congrArg (fun f : NonUnitalModuleHom S ℤ ℤ => f 1) e
    exact one_ne_zero bad
  · intro r
    exact sourceAction_toEndHom_eq_zero _ (fun _ _ => rfl) r
  · intro t
    exact targetAction_toEndHom_eq_zero _ (fun _ _ => rfl) t

end IntegerZero

/-- The identity additive map in the integer regular model exposes the multiplication side. -/
example (a b : ℤ) :
    letI : NonUnitalModule ℤ ℤ := NonUnitalModule.regular ℤ
    let φ : RegularModuleHom ℤ ℤ := ⟨AddMonoidHom.id ℤ, fun _ _ => rfl⟩
    fromRegular ((a : ℤ) • φ) b = b * a := rfl

end Langlands.Algebra.NonUnitalBimoduleHomActions
