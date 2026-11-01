import Langlands.Algebra.NonUnitalBimodule

/-!
# Residual original actions on actual Hom spaces

Internal arbitrary-ring prerequisites for Renard I.2.2–I.2.3. All actions
use the published original Hom carrier, group and composition.
-/

set_option autoImplicit false

open CategoryTheory MulOpposite

namespace Langlands.Algebra.NonUnitalBimoduleHomActions

universe uS uR uT uY uZ uY' uZ'

section Composition

variable {S : Type uS} [NonUnitalRing S]
  {Y : Type uY} {Z : Type uZ} {Y' : Type uY'} {Z' : Type uZ'}
  [AddCommGroup Y] [AddCommGroup Z] [AddCommGroup Y'] [AddCommGroup Z']
  [NonUnitalModule S Y] [NonUnitalModule S Z]
  [NonUnitalModule S Y'] [NonUnitalModule S Z']

/-- Precomposition using exactly the original Hom composition. -/
def precomposeAddHom (f : NonUnitalModuleHom S Y' Y) :
    NonUnitalModuleHom S Y Z →+ NonUnitalModuleHom S Y' Z where
  toFun h := h.comp f
  map_zero' := by ext y; rfl
  map_add' _ _ := by ext y; rfl

/-- Postcomposition using exactly the original Hom composition. -/
def postcomposeAddHom (g : NonUnitalModuleHom S Z Z') :
    NonUnitalModuleHom S Y Z →+ NonUnitalModuleHom S Y Z' where
  toFun h := g.comp h
  map_zero' := by ext y; exact g.map_zero
  map_add' h k := by ext y; exact g.map_add (h y) (k y)

/-- The actual additive map `h ↦ g ∘ h ∘ f`. -/
def mapAddHom (f : NonUnitalModuleHom S Y' Y) (g : NonUnitalModuleHom S Z Z') :
    NonUnitalModuleHom S Y Z →+ NonUnitalModuleHom S Y' Z' :=
  (postcomposeAddHom g).comp (precomposeAddHom f)

@[simp] theorem precomposeAddHom_apply (f : NonUnitalModuleHom S Y' Y)
    (h : NonUnitalModuleHom S Y Z) : precomposeAddHom f h = h.comp f := rfl

@[simp] theorem postcomposeAddHom_apply (g : NonUnitalModuleHom S Z Z')
    (h : NonUnitalModuleHom S Y Z) : postcomposeAddHom g h = g.comp h := rfl

@[simp] theorem mapAddHom_apply (f : NonUnitalModuleHom S Y' Y)
    (g : NonUnitalModuleHom S Z Z') (h : NonUnitalModuleHom S Y Z) :
    mapAddHom f g h = g.comp (h.comp f) := rfl

end Composition

section Source

variable {S : Type uS} {R : Type uR} {Y : Type uY} {Z : Type uZ}
  [NonUnitalRing S] [NonUnitalRing R] [AddCommGroup Y] [AddCommGroup Z]
  [NonUnitalModule S Y] [NonUnitalModule Rᵐᵒᵖ Y] [NonUnitalModule S Z]
  (hY : ActionsCommute S R Y)

/-- Left `R` action by precomposition with the right `R` action on the source. -/
abbrev sourceAction : NonUnitalModule R (NonUnitalModuleHom S Y Z) where
  smul r h := h.comp (hY.rightActionHom (op r))
  smul_zero _ := by ext y; rfl
  smul_add _ _ _ := by ext y; rfl
  mul_smul r s h := by
    ext y
    change h (op (r * s) • y) = h (op s • (op r • y))
    rw [right_mul_smul]
  add_smul r s h := by
    ext y
    change h (op (r + s) • y) = h (op r • y) + h (op s • y)
    rw [op_add, NonUnitalModule.add_smul, h.map_add]
  zero_smul h := by
    ext y
    change h (op (0 : R) • y) = 0
    rw [op_zero, NonUnitalModule.zero_smul, h.map_zero]

/-- The entire scalar endomorphism is original-Hom precomposition. -/
theorem sourceAction_toEndHom (r : R) :
    NonUnitalModule.toEndHom (sourceAction (Z := Z) hY) r =
      precomposeAddHom (hY.rightActionHom (op r)) := rfl

@[simp] theorem sourceAction_smul (r : R) (h : NonUnitalModuleHom S Y Z) (y : Y) :
    letI := sourceAction (Z := Z) hY
    (r • h) y = h (op r • y) := rfl

end Source

section Target

variable {S : Type uS} {T : Type uT} {Y : Type uY} {Z : Type uZ}
  [NonUnitalRing S] [NonUnitalRing T] [AddCommGroup Y] [AddCommGroup Z]
  [NonUnitalModule S Y] [NonUnitalModule S Z] [NonUnitalModule Tᵐᵒᵖ Z]
  (hZ : ActionsCommute S T Z)

/-- Right `T` action by postcomposition with the right `T` action on the target. -/
abbrev targetAction : NonUnitalModule Tᵐᵒᵖ (NonUnitalModuleHom S Y Z) where
  smul t h := (hZ.rightActionHom t).comp h
  smul_zero t := by ext y; exact smul_zero t
  smul_add t h k := by ext y; exact smul_add t (h y) (k y)
  mul_smul t s h := by ext y; exact mul_smul t s (h y)
  add_smul t s h := by ext y; exact NonUnitalModule.add_smul t s (h y)
  zero_smul h := by ext y; exact NonUnitalModule.zero_smul (h y)

/-- The entire scalar endomorphism is original-Hom postcomposition. -/
theorem targetAction_toEndHom (t : Tᵐᵒᵖ) :
    NonUnitalModule.toEndHom (targetAction (Y := Y) hZ) t =
      postcomposeAddHom (hZ.rightActionHom t) := rfl

@[simp] theorem targetAction_smul (t : Tᵐᵒᵖ) (h : NonUnitalModuleHom S Y Z) (y : Y) :
    letI := targetAction (Y := Y) hZ
    (t • h) y = t • h y := rfl

end Target

section Both

variable {S : Type uS} {R : Type uR} {T : Type uT} {Y : Type uY} {Z : Type uZ}
  [NonUnitalRing S] [NonUnitalRing R] [NonUnitalRing T]
  [AddCommGroup Y] [AddCommGroup Z]
  [NonUnitalModule S Y] [NonUnitalModule Rᵐᵒᵖ Y]
  [NonUnitalModule S Z] [NonUnitalModule Tᵐᵒᵖ Z]
  (hY : ActionsCommute S R Y) (hZ : ActionsCommute S T Z)

/-- Precomposition and postcomposition commute on the actual original Hom. -/
theorem actionsCommute :
    @ActionsCommute R T (NonUnitalModuleHom S Y Z) _ _ _ (sourceAction hY) (targetAction hZ) := by
  intro r t h
  ext y
  rfl

/-- Exactly the original Hom carrier and group with the two named residual actions. -/
def hom : NonUnitalBimoduleCat.{uR, uT, max uY uZ} R T :=
  @NonUnitalBimoduleCat.of R T _ _ (NonUnitalModuleHom S Y Z) _
    (sourceAction hY) (targetAction hZ) (actionsCommute hY hZ)

theorem hom_carrier : (hom hY hZ).carrier = NonUnitalModuleHom S Y Z := rfl

theorem hom_isAddCommGroup : (hom hY hZ).isAddCommGroup =
    NonUnitalModuleHom.instAddCommGroup (A := S) (M := Y) (N := Z) := rfl

theorem hom_isLeftModule : (hom hY hZ).isLeftModule = sourceAction hY := rfl

theorem hom_isRightModule : (hom hY hZ).isRightModule = targetAction hZ := rfl

theorem hom_left_toEndHom (r : R) :
    NonUnitalModule.toEndHom (hom hY hZ).isLeftModule r =
      precomposeAddHom (hY.rightActionHom (op r)) := rfl

theorem hom_right_toEndHom (t : Tᵐᵒᵖ) :
    NonUnitalModule.toEndHom (hom hY hZ).isRightModule t =
      postcomposeAddHom (hZ.rightActionHom t) := rfl

end Both

section RightSource

variable {R : Type uR} {S : Type uS} {Y : Type uY} {Z : Type uZ}
  [NonUnitalRing R] [NonUnitalRing S] [AddCommGroup Y] [AddCommGroup Z]
  [NonUnitalModule R Y] [NonUnitalModule Sᵐᵒᵖ Y] [NonUnitalModule Sᵐᵒᵖ Z]
  (hY : ActionsCommute R S Y)

/-- Right `R` action on right `S`-linear maps, directly from the supplied left action. -/
abbrev rightSourceAction : NonUnitalModule Rᵐᵒᵖ (NonUnitalModuleHom Sᵐᵒᵖ Y Z) where
  smul r h := h.comp (hY.leftActionHom r.unop)
  smul_zero _ := by ext y; rfl
  smul_add _ _ _ := by ext y; rfl
  mul_smul r s h := by
    ext y
    change h ((s.unop * r.unop) • y) = h (s.unop • (r.unop • y))
    rw [mul_smul]
  add_smul r s h := by
    ext y
    change h ((r.unop + s.unop) • y) = h (r.unop • y) + h (s.unop • y)
    rw [NonUnitalModule.add_smul, h.map_add]
  zero_smul h := by
    ext y
    change h ((0 : R) • y) = 0
    rw [NonUnitalModule.zero_smul, h.map_zero]

/-- The complete scalar endomorphism uses the published left-action Hom. -/
theorem rightSourceAction_toEndHom (r : Rᵐᵒᵖ) :
    NonUnitalModule.toEndHom (rightSourceAction (Z := Z) hY) r =
      precomposeAddHom (hY.leftActionHom r.unop) := rfl

@[simp] theorem rightSourceAction_smul (r : R) (h : NonUnitalModuleHom Sᵐᵒᵖ Y Z) (y : Y) :
    letI := rightSourceAction (Z := Z) hY
    (op r • h) y = h (r • y) := rfl

end RightSource

section Regular

variable {A : Type uS} [NonUnitalRing A] {M : Type uZ} [AddCommGroup M]
  [hM : NonUnitalModule A M]

/-- Specialize the source action to exactly the supplied left/right regular actions. -/
abbrev regularSourceAction :
    NonUnitalModule A (@NonUnitalModuleHom A A M _ _ _ (NonUnitalModule.regular A) hM) :=
  @sourceAction A A A M _ _ _ _ (NonUnitalModule.regular A)
    (NonUnitalModule.rightRegular A) hM (NonUnitalModule.regular_actionsCommute A)

local instance regularHomModule :
    NonUnitalModule A
      (@NonUnitalModuleHom A A M _ _ _ (NonUnitalModule.regular A) hM) :=
  regularSourceAction

/-- The original regular-Hom additive equivalence is left-linear for the residual action. -/
def fromRegular :
    @NonUnitalModuleHom A (RegularModuleHom A M)
      (@NonUnitalModuleHom A A M _ _ _ (NonUnitalModule.regular A) hM) _ _ _
      RegularModuleHom.instNonUnitalModule regularSourceAction where
  toAddMonoidHom := (RegularModuleHom.equivNonUnitalModuleHom (A := A) (M := M)).toAddMonoidHom
  map_smul' _ _ := rfl

/-- Its actual inverse is also original left-linear. -/
def toRegular :
    @NonUnitalModuleHom A
      (@NonUnitalModuleHom A A M _ _ _ (NonUnitalModule.regular A) hM)
      (RegularModuleHom A M) _ _ _ regularSourceAction
      RegularModuleHom.instNonUnitalModule where
  toAddMonoidHom :=
    (RegularModuleHom.equivNonUnitalModuleHom (A := A) (M := M)).symm.toAddMonoidHom
  map_smul' _ _ := rfl

theorem fromRegular_toAddMonoidHom :
    (fromRegular (A := A) (M := M)).toAddMonoidHom =
      (RegularModuleHom.equivNonUnitalModuleHom (A := A) (M := M)).toAddMonoidHom := rfl

theorem toRegular_toAddMonoidHom :
    (toRegular (A := A) (M := M)).toAddMonoidHom =
      (RegularModuleHom.equivNonUnitalModuleHom (A := A) (M := M)).symm.toAddMonoidHom := rfl

/-- Whole original-Hom inverse identity on the published regular model. -/
theorem toRegular_comp_fromRegular :
    (toRegular (A := A) (M := M)).comp fromRegular =
      NonUnitalModuleHom.id A (RegularModuleHom A M) := rfl

/-- Whole original-Hom inverse identity on exactly the original Hom carrier. -/
theorem fromRegular_comp_toRegular :
    (fromRegular (A := A) (M := M)).comp toRegular =
      @NonUnitalModuleHom.id A
        (@NonUnitalModuleHom A A M _ _ _ (NonUnitalModule.regular A) hM)
        _ _ regularSourceAction := rfl

/-- The general scalar endomorphism is intertwined with the existing regular source action. -/
theorem regularSourceAction_compat (a : A) :
    (NonUnitalModule.toEndHom (regularSourceAction (A := A) (M := M)) a).comp
        (RegularModuleHom.equivNonUnitalModuleHom (A := A) (M := M)).toAddMonoidHom =
      (RegularModuleHom.equivNonUnitalModuleHom (A := A) (M := M)).toAddMonoidHom.comp
        (NonUnitalModule.toEndHom
          (RegularModuleHom.instNonUnitalModule (A := A) (M := M)) a) := rfl

/-- Side and order remain visible over arbitrary, possibly noncommutative rings. -/
theorem regularSourceAction_apply (a b : A)
    (h : @NonUnitalModuleHom A A M _ _ _ (NonUnitalModule.regular A) hM) :
    letI := regularSourceAction (A := A) (M := M)
    (a • h) b = h (b * a) := rfl

/-- Source precomposition fixes the multiplication order without commutativity. -/
theorem regularSourceAction_mul_apply (a c b : A)
    (h : @NonUnitalModuleHom A A M _ _ _ (NonUnitalModule.regular A) hM) :
    letI := regularSourceAction (A := A) (M := M)
    ((a * c) • h) b = h ((b * a) * c) := by
  change h (b * (a * c)) = h ((b * a) * c)
  rw [mul_assoc]

end Regular

section Degenerate

variable {S : Type uS} {R : Type uR} {T : Type uT} {Y : Type uY} {Z : Type uZ}
  [NonUnitalRing S] [NonUnitalRing R] [NonUnitalRing T]
  [AddCommGroup Y] [AddCommGroup Z]
  [NonUnitalModule S Y] [NonUnitalModule S Z]

/-- A zero residual source action gives zero endomorphisms on the entire Hom. -/
theorem sourceAction_toEndHom_eq_zero [NonUnitalModule Rᵐᵒᵖ Y]
    (hY : ActionsCommute S R Y) (hz : ∀ (r : R) (y : Y), op r • y = 0) (r : R) :
    NonUnitalModule.toEndHom (sourceAction (Z := Z) hY) r = 0 := by
  apply AddMonoidHom.ext
  intro h
  apply NonUnitalModuleHom.ext
  intro y
  change h (op r • y) = 0
  rw [hz, h.map_zero]

/-- A zero residual target action gives zero endomorphisms on the entire Hom. -/
theorem targetAction_toEndHom_eq_zero [NonUnitalModule Tᵐᵒᵖ Z]
    (hZ : ActionsCommute S T Z) (hz : ∀ (t : Tᵐᵒᵖ) (z : Z), t • z = 0) (t : Tᵐᵒᵖ) :
    NonUnitalModule.toEndHom (targetAction (Y := Y) hZ) t = 0 := by
  apply AddMonoidHom.ext
  intro h
  apply NonUnitalModuleHom.ext
  intro y
  exact hz t (h y)

/-- A subsingleton target makes the actual Hom subsingleton, for any original actions. -/
theorem hom_subsingleton [Subsingleton Z] : Subsingleton (NonUnitalModuleHom S Y Z) :=
  ⟨fun _ _ => NonUnitalModuleHom.ext fun _ => Subsingleton.elim _ _⟩

/-- A subsingleton source also makes the actual Hom subsingleton. -/
theorem hom_subsingleton_of_source [Subsingleton Y] :
    Subsingleton (NonUnitalModuleHom S Y Z) := by
  refine ⟨fun f g => NonUnitalModuleHom.ext fun y => ?_⟩
  rw [Subsingleton.elim y 0, f.map_zero, g.map_zero]

end Degenerate

end Langlands.Algebra.NonUnitalBimoduleHomActions
