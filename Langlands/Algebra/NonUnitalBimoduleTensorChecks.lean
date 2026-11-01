import Langlands.Algebra.NonUnitalBimoduleTensor

/-!
# Interface and boundary checks for original bimodule tensors

Internal checks for the constructions in `NonUnitalBimoduleTensor`, retaining
independent universes and original structures. Source and scope are documented
in the same-stem Markdown file.
-/

set_option autoImplicit false

namespace Langlands.Algebra.NonUnitalBimoduleTensorChecks

open CategoryTheory MulOpposite
open Langlands.Algebra.NonUnitalBimoduleTensor
open Langlands.Algebra.NonUnitalModuleTensor (Tensor tmul)

universe uS uR uT uX uY uZ uX' uY' uX'' uY''

/-! Full unapplied telescopes: the term after `:=` is always the named declaration.
The binders retain the names of arguments used implicitly by those declarations. -/

section Interfaces
set_option linter.unusedVariables false

example : ∀ {S : Type uS} {R : Type uR} [NonUnitalRing S] [NonUnitalRing R]
    {X : Type uX} [AddCommGroup X] [NonUnitalModule S X] [NonUnitalModule Rᵐᵒᵖ X]
    (hX : ActionsCommute S R X) (Y : Type uY) [AddCommGroup Y] [NonUnitalModule R Y],
    S → (Tensor R X Y →+ Tensor R X Y) := @leftScalar

example : ∀ {S : Type uS} {R : Type uR} [NonUnitalRing S] [NonUnitalRing R]
    {X : Type uX} [AddCommGroup X] [NonUnitalModule S X] [NonUnitalModule Rᵐᵒᵖ X]
    (hX : ActionsCommute S R X) (Y : Type uY) [AddCommGroup Y] [NonUnitalModule R Y],
    NonUnitalModule S (Tensor R X Y) := @leftModule

example : ∀ {S : Type uS} {R : Type uR} [NonUnitalRing S] [NonUnitalRing R]
    {X : Type uX} [AddCommGroup X] [NonUnitalModule S X] [NonUnitalModule Rᵐᵒᵖ X]
    (hX : ActionsCommute S R X) (Y : Type uY) [AddCommGroup Y] [NonUnitalModule R Y] (s : S),
    NonUnitalModule.toEndHom (leftModule hX Y) s =
      NonUnitalModuleTensor.map R (hX.leftActionHom s) (NonUnitalModuleHom.id R Y) := @toEndHom_leftModule

example : ∀ {R : Type uR} {T : Type uT} [NonUnitalRing R] [NonUnitalRing T]
    (X : Type uX) [AddCommGroup X] [NonUnitalModule Rᵐᵒᵖ X]
    {Y : Type uY} [AddCommGroup Y] [NonUnitalModule R Y] [NonUnitalModule Tᵐᵒᵖ Y]
    (hY : ActionsCommute R T Y),
    Tᵐᵒᵖ → (Tensor R X Y →+ Tensor R X Y) := @rightScalar

example : ∀ {R : Type uR} {T : Type uT} [NonUnitalRing R] [NonUnitalRing T]
    (X : Type uX) [AddCommGroup X] [NonUnitalModule Rᵐᵒᵖ X]
    {Y : Type uY} [AddCommGroup Y] [NonUnitalModule R Y] [NonUnitalModule Tᵐᵒᵖ Y]
    (hY : ActionsCommute R T Y),
    NonUnitalModule Tᵐᵒᵖ (Tensor R X Y) := @rightModule

example : ∀ {R : Type uR} {T : Type uT} [NonUnitalRing R] [NonUnitalRing T]
    (X : Type uX) [AddCommGroup X] [NonUnitalModule Rᵐᵒᵖ X]
    {Y : Type uY} [AddCommGroup Y] [NonUnitalModule R Y] [NonUnitalModule Tᵐᵒᵖ Y]
    (hY : ActionsCommute R T Y) (t : Tᵐᵒᵖ),
    NonUnitalModule.toEndHom (rightModule X hY) t =
      NonUnitalModuleTensor.map R (NonUnitalModuleHom.id Rᵐᵒᵖ X) (hY.rightActionHom t) := @toEndHom_rightModule

example : ∀ {S : Type uS} {R : Type uR} {T : Type uT}
    [NonUnitalRing S] [NonUnitalRing R] [NonUnitalRing T]
    {X : Type uX} [AddCommGroup X] [NonUnitalModule S X] [NonUnitalModule Rᵐᵒᵖ X]
    {Y : Type uY} [AddCommGroup Y] [NonUnitalModule R Y] [NonUnitalModule Tᵐᵒᵖ Y]
    (hX : ActionsCommute S R X) (hY : ActionsCommute R T Y),
    @ActionsCommute S T (Tensor R X Y) _ _ _ (leftModule hX Y) (rightModule X hY) := @actionsCommute

example : ∀ {S : Type uS} {R : Type uR} {T : Type uT}
    [NonUnitalRing S] [NonUnitalRing R] [NonUnitalRing T]
    {X : Type uX} [AddCommGroup X] [NonUnitalModule S X] [NonUnitalModule Rᵐᵒᵖ X]
    {Y : Type uY} [AddCommGroup Y] [NonUnitalModule R Y] [NonUnitalModule Tᵐᵒᵖ Y]
    (hX : ActionsCommute S R X) (hY : ActionsCommute R T Y),
    NonUnitalBimoduleCat.{uS, uT, max uX uY} S T := @bimodule

example : ∀ {S : Type uS} {R : Type uR} {T : Type uT}
    [NonUnitalRing S] [NonUnitalRing R] [NonUnitalRing T]
    {X : Type uX} [AddCommGroup X] [NonUnitalModule S X] [NonUnitalModule Rᵐᵒᵖ X]
    {Y : Type uY} [AddCommGroup Y] [NonUnitalModule R Y] [NonUnitalModule Tᵐᵒᵖ Y]
    (hX : ActionsCommute S R X) (hY : ActionsCommute R T Y),
    (bimodule hX hY).carrier = Tensor R X Y := @bimodule_carrier

example : ∀ {S : Type uS} {R : Type uR} {T : Type uT}
    [NonUnitalRing S] [NonUnitalRing R] [NonUnitalRing T]
    {X : Type uX} [AddCommGroup X] [NonUnitalModule S X] [NonUnitalModule Rᵐᵒᵖ X]
    {Y : Type uY} [AddCommGroup Y] [NonUnitalModule R Y] [NonUnitalModule Tᵐᵒᵖ Y]
    (hX : ActionsCommute S R X) (hY : ActionsCommute R T Y),
    (bimodule hX hY).isAddCommGroup = NonUnitalModuleTensor.addCommGroup R X Y := @bimodule_isAddCommGroup

example : ∀ {S : Type uS} {R : Type uR} {T : Type uT}
    [NonUnitalRing S] [NonUnitalRing R] [NonUnitalRing T]
    {X : Type uX} [AddCommGroup X] [NonUnitalModule S X] [NonUnitalModule Rᵐᵒᵖ X]
    {Y : Type uY} [AddCommGroup Y] [NonUnitalModule R Y] [NonUnitalModule Tᵐᵒᵖ Y]
    (hX : ActionsCommute S R X) (hY : ActionsCommute R T Y),
    (bimodule hX hY).isLeftModule = leftModule hX Y := @bimodule_isLeftModule

example : ∀ {S : Type uS} {R : Type uR} {T : Type uT}
    [NonUnitalRing S] [NonUnitalRing R] [NonUnitalRing T]
    {X : Type uX} [AddCommGroup X] [NonUnitalModule S X] [NonUnitalModule Rᵐᵒᵖ X]
    {Y : Type uY} [AddCommGroup Y] [NonUnitalModule R Y] [NonUnitalModule Tᵐᵒᵖ Y]
    (hX : ActionsCommute S R X) (hY : ActionsCommute R T Y),
    (bimodule hX hY).isRightModule = rightModule X hY := @bimodule_isRightModule

example : ∀ {S : Type uS} {R : Type uR} {T : Type uT}
    [NonUnitalRing S] [NonUnitalRing R] [NonUnitalRing T] (X : NonUnitalBimoduleCat.{uS, uR, uX} S R) (Y : NonUnitalBimoduleCat.{uR, uT, uY} R T),
    NonUnitalBimoduleCat.{uS, uT, max uX uY} S T := @tensor

example : ∀ {S : Type uS} {R : Type uR} {T : Type uT}
    [NonUnitalRing S] [NonUnitalRing R] [NonUnitalRing T]
    {X : NonUnitalBimoduleCat.{uS, uR, uX} S R} {X' : NonUnitalBimoduleCat.{uS, uR, uX'} S R}
    {Y : NonUnitalBimoduleCat.{uR, uT, uY} R T} {Y' : NonUnitalBimoduleCat.{uR, uT, uY'} R T},
    NonUnitalBimoduleHom S R X X' → NonUnitalBimoduleHom R T Y Y' →
      NonUnitalBimoduleHom S T (tensor X Y) (tensor X' Y') := @map

example : ∀ {S : Type uS} {R : Type uR} {T : Type uT}
    [NonUnitalRing S] [NonUnitalRing R] [NonUnitalRing T]
    {X : NonUnitalBimoduleCat.{uS, uR, uX} S R} {X' : NonUnitalBimoduleCat.{uS, uR, uX'} S R}
    {Y : NonUnitalBimoduleCat.{uR, uT, uY} R T} {Y' : NonUnitalBimoduleCat.{uR, uT, uY'} R T} (f : NonUnitalBimoduleHom S R X X') (g : NonUnitalBimoduleHom R T Y Y'),
    (map f g).val = NonUnitalModuleTensor.map R f.toRightHom g.toLeftHom := @map_val

example : ∀ {S : Type uS} {R : Type uR} {T : Type uT}
    [NonUnitalRing S] [NonUnitalRing R] [NonUnitalRing T]
    {X : NonUnitalBimoduleCat.{uS, uR, uX} S R} {X' : NonUnitalBimoduleCat.{uS, uR, uX'} S R}
    {Y : NonUnitalBimoduleCat.{uR, uT, uY} R T} {Y' : NonUnitalBimoduleCat.{uR, uT, uY'} R T} (f : NonUnitalBimoduleHom S R X X') (g : NonUnitalBimoduleHom R T Y Y'),
    (map f g).toLeftHom = leftMap X.actionsCommute X'.actionsCommute f g.toLeftHom := @map_toLeftHom

example : ∀ {S : Type uS} {R : Type uR} {T : Type uT}
    [NonUnitalRing S] [NonUnitalRing R] [NonUnitalRing T]
    {X : NonUnitalBimoduleCat.{uS, uR, uX} S R} {X' : NonUnitalBimoduleCat.{uS, uR, uX'} S R}
    {Y : NonUnitalBimoduleCat.{uR, uT, uY} R T} {Y' : NonUnitalBimoduleCat.{uR, uT, uY'} R T} (f : NonUnitalBimoduleHom S R X X') (g : NonUnitalBimoduleHom R T Y Y'),
    (map f g).toRightHom = rightMap Y.actionsCommute Y'.actionsCommute f.toRightHom g := @map_toRightHom

example : ∀ {S : Type uS} {R : Type uR} {T : Type uT}
    [NonUnitalRing S] [NonUnitalRing R] [NonUnitalRing T] {X : NonUnitalBimoduleCat.{uS, uR, uX} S R} {Y : NonUnitalBimoduleCat.{uR, uT, uY} R T},
    map (NonUnitalBimoduleHom.id S R X) (NonUnitalBimoduleHom.id R T Y) =
      NonUnitalBimoduleHom.id S T (tensor X Y) := @map_id

example : ∀ {S : Type uS} {R : Type uR} {T : Type uT}
    [NonUnitalRing S] [NonUnitalRing R] [NonUnitalRing T]
    {X : NonUnitalBimoduleCat.{uS, uR, uX} S R} {X' : NonUnitalBimoduleCat.{uS, uR, uX'} S R} {X'' : NonUnitalBimoduleCat.{uS, uR, uX''} S R}
    {Y : NonUnitalBimoduleCat.{uR, uT, uY} R T} {Y' : NonUnitalBimoduleCat.{uR, uT, uY'} R T} {Y'' : NonUnitalBimoduleCat.{uR, uT, uY''} R T} (f : NonUnitalBimoduleHom S R X X') (g : NonUnitalBimoduleHom R T Y Y')
    (f' : NonUnitalBimoduleHom S R X' X'') (g' : NonUnitalBimoduleHom R T Y' Y''),
    (map f' g').comp (map f g) = map (f'.comp f) (g'.comp g) := @map_comp

example : ∀ {S : Type uS} {R : Type uR} {T : Type uT}
    [NonUnitalRing S] [NonUnitalRing R] [NonUnitalRing T]
    {X : NonUnitalBimoduleCat.{uS, uR, uX} S R} {X' : NonUnitalBimoduleCat.{uS, uR, uX'} S R}
    {Y : NonUnitalBimoduleCat.{uR, uT, uY} R T} {Y' : NonUnitalBimoduleCat.{uR, uT, uY'} R T}
    (f₁ f₂ : NonUnitalBimoduleHom S R X X') (g : NonUnitalBimoduleHom R T Y Y'),
    map (f₁ + f₂) g = map f₁ g + map f₂ g := @map_add_left

example : ∀ {S : Type uS} {R : Type uR} {T : Type uT}
    [NonUnitalRing S] [NonUnitalRing R] [NonUnitalRing T]
    {X : NonUnitalBimoduleCat.{uS, uR, uX} S R} {X' : NonUnitalBimoduleCat.{uS, uR, uX'} S R}
    {Y : NonUnitalBimoduleCat.{uR, uT, uY} R T} {Y' : NonUnitalBimoduleCat.{uR, uT, uY'} R T} (f : NonUnitalBimoduleHom S R X X')
    (g₁ g₂ : NonUnitalBimoduleHom R T Y Y'),
    map f (g₁ + g₂) = map f g₁ + map f g₂ := @map_add_right

example : ∀ {S : Type uS} {R : Type uR} {T : Type uT}
    [NonUnitalRing S] [NonUnitalRing R] [NonUnitalRing T] (X₀ : NonUnitalBimoduleCat.{uS, uR, uX} S R),
    NonUnitalBimoduleCat.{uR, uT, uY} R T ⥤ NonUnitalBimoduleCat.{uS, uT, max uX uY} S T := @tensorLeft

example : ∀ {S : Type uS} {R : Type uR} {T : Type uT}
    [NonUnitalRing S] [NonUnitalRing R] [NonUnitalRing T] (Y₀ : NonUnitalBimoduleCat.{uR, uT, uY} R T),
    NonUnitalBimoduleCat.{uS, uR, uX} S R ⥤ NonUnitalBimoduleCat.{uS, uT, max uX uY} S T := @tensorRight

example : ∀ {S : Type uS} {R : Type uR} {T : Type uT}
    [NonUnitalRing S] [NonUnitalRing R] [NonUnitalRing T] (X₀ : NonUnitalBimoduleCat.{uS, uR, uX} S R),
    (tensorLeft X₀ : NonUnitalBimoduleCat.{uR, uT, uY} R T ⥤ NonUnitalBimoduleCat.{uS, uT, max uX uY} S T).Additive := @tensorLeft_additive

example : ∀ {S : Type uS} {R : Type uR} {T : Type uT}
    [NonUnitalRing S] [NonUnitalRing R] [NonUnitalRing T] (Y₀ : NonUnitalBimoduleCat.{uR, uT, uY} R T),
    (tensorRight Y₀ : NonUnitalBimoduleCat.{uS, uR, uX} S R ⥤ NonUnitalBimoduleCat.{uS, uT, max uX uY} S T).Additive := @tensorRight_additive

example : ∀ {S : Type uS} {R : Type uR} {T : Type uT}
    [NonUnitalRing S] [NonUnitalRing R] [NonUnitalRing T] (X₀ : NonUnitalBimoduleCat.{uS, uR, uX} S R) (Y : NonUnitalBimoduleCat.{uR, uT, uY} R T),
    (tensorLeft X₀).obj Y = tensor X₀ Y := @tensorLeft_obj

example : ∀ {S : Type uS} {R : Type uR} {T : Type uT}
    [NonUnitalRing S] [NonUnitalRing R] [NonUnitalRing T] (Y₀ : NonUnitalBimoduleCat.{uR, uT, uY} R T) (X : NonUnitalBimoduleCat.{uS, uR, uX} S R),
    (tensorRight Y₀).obj X = tensor X Y₀ := @tensorRight_obj

example : ∀ {S : Type uS} {R : Type uR} {T : Type uT}
    [NonUnitalRing S] [NonUnitalRing R] [NonUnitalRing T] (X₀ : NonUnitalBimoduleCat.{uS, uR, uX} S R) {Y Y' : NonUnitalBimoduleCat.{uR, uT, uY} R T} (g : Y ⟶ Y'),
    (tensorLeft X₀).map g = map (NonUnitalBimoduleHom.id S R X₀) g := @tensorLeft_map

example : ∀ {S : Type uS} {R : Type uR} {T : Type uT}
    [NonUnitalRing S] [NonUnitalRing R] [NonUnitalRing T] (Y₀ : NonUnitalBimoduleCat.{uR, uT, uY} R T) {X X' : NonUnitalBimoduleCat.{uS, uR, uX} S R} (f : X ⟶ X'),
    (tensorRight Y₀).map f = map f (NonUnitalBimoduleHom.id R T Y₀) := @tensorRight_map

example : ∀ {S : Type uS} {R : Type uR} [NonUnitalRing S] [NonUnitalRing R]
    {X : Type uX} [AddCommGroup X] [NonUnitalModule S X] [NonUnitalModule Rᵐᵒᵖ X]
    (hX : ActionsCommute S R X) {Y : Type uY} [AddCommGroup Y] [NonUnitalModule R Y]
    {Z : Type uZ} [AddCommGroup Z] [NonUnitalModule S Z]
    (b : X →+ Y →+ Z) (hb : NonUnitalModuleTensor.IsBalanced R b)
    (hs : ∀ (s : S) (x : X) (y : Y), b (s • x) y = s • b x y),
    @NonUnitalModuleHom S (Tensor R X Y) Z _ _ _ (leftModule hX Y) _ := @leftLift

example : ∀ {R : Type uR} {T : Type uT} [NonUnitalRing R] [NonUnitalRing T]
    {X : Type uX} [AddCommGroup X] [NonUnitalModule Rᵐᵒᵖ X]
    {Y : Type uY} [AddCommGroup Y] [NonUnitalModule R Y] [NonUnitalModule Tᵐᵒᵖ Y]
    (hY : ActionsCommute R T Y) {Z : Type uZ} [AddCommGroup Z] [NonUnitalModule Tᵐᵒᵖ Z]
    (b : X →+ Y →+ Z) (hb : NonUnitalModuleTensor.IsBalanced R b)
    (ht : ∀ (t : Tᵐᵒᵖ) (x : X) (y : Y), b x (t • y) = t • b x y),
    @NonUnitalModuleHom Tᵐᵒᵖ (Tensor R X Y) Z _ _ _ (rightModule X hY) _ := @rightLift

example : ∀ {S : Type uS} {R : Type uR} {T : Type uT}
    [NonUnitalRing S] [NonUnitalRing R] [NonUnitalRing T]
    {X : NonUnitalBimoduleCat.{uS, uR, uX} S R} {Y : NonUnitalBimoduleCat.{uR, uT, uY} R T} {Z : NonUnitalBimoduleCat.{uS, uT, uZ} S T}
    (b : X →+ Y →+ Z) (hb : NonUnitalModuleTensor.IsBalanced R b)
    (hs : ∀ (s : S) (x : X) (y : Y), b (s • x) y = s • b x y)
    (ht : ∀ (t : Tᵐᵒᵖ) (x : X) (y : Y), b x (t • y) = t • b x y),
    NonUnitalBimoduleHom S T (tensor X Y) Z := @lift

example : ∀ {S : Type uS} {R : Type uR} {T : Type uT}
    [NonUnitalRing S] [NonUnitalRing R] [NonUnitalRing T]
    {X : NonUnitalBimoduleCat.{uS, uR, uX} S R} {Y : NonUnitalBimoduleCat.{uR, uT, uY} R T} {Z : NonUnitalBimoduleCat.{uS, uT, uZ} S T}
    (b : X →+ Y →+ Z) (hb : NonUnitalModuleTensor.IsBalanced R b)
    (hs : ∀ (s : S) (x : X) (y : Y), b (s • x) y = s • b x y)
    (ht : ∀ (t : Tᵐᵒᵖ) (x : X) (y : Y), b x (t • y) = t • b x y),
    (lift b hb hs ht).val = NonUnitalModuleTensor.lift R b hb := @lift_val

example : ∀ {S : Type uS} {R : Type uR} {T : Type uT}
    [NonUnitalRing S] [NonUnitalRing R] [NonUnitalRing T]
    {X : NonUnitalBimoduleCat.{uS, uR, uX} S R} {Y : NonUnitalBimoduleCat.{uR, uT, uY} R T} {Z : NonUnitalBimoduleCat.{uS, uT, uZ} S T}
    (b : X →+ Y →+ Z) (hb : NonUnitalModuleTensor.IsBalanced R b)
    (hs : ∀ (s : S) (x : X) (y : Y), b (s • x) y = s • b x y)
    (ht : ∀ (t : Tᵐᵒᵖ) (x : X) (y : Y), b x (t • y) = t • b x y),
    (lift b hb hs ht).toLeftHom = leftLift X.actionsCommute b hb hs := @lift_toLeftHom

example : ∀ {S : Type uS} {R : Type uR} {T : Type uT}
    [NonUnitalRing S] [NonUnitalRing R] [NonUnitalRing T]
    {X : NonUnitalBimoduleCat.{uS, uR, uX} S R} {Y : NonUnitalBimoduleCat.{uR, uT, uY} R T} {Z : NonUnitalBimoduleCat.{uS, uT, uZ} S T}
    (b : X →+ Y →+ Z) (hb : NonUnitalModuleTensor.IsBalanced R b)
    (hs : ∀ (s : S) (x : X) (y : Y), b (s • x) y = s • b x y)
    (ht : ∀ (t : Tᵐᵒᵖ) (x : X) (y : Y), b x (t • y) = t • b x y),
    (lift b hb hs ht).toRightHom = rightLift Y.actionsCommute b hb ht := @lift_toRightHom

example : ∀ {S : Type uS} {R : Type uR} {T : Type uT}
    [NonUnitalRing S] [NonUnitalRing R] [NonUnitalRing T]
    {X : NonUnitalBimoduleCat.{uS, uR, uX} S R} {Y : NonUnitalBimoduleCat.{uR, uT, uY} R T} {Z : NonUnitalBimoduleCat.{uS, uT, uZ} S T}
    (b : X →+ Y →+ Z) (hb : NonUnitalModuleTensor.IsBalanced R b)
    (hs : ∀ (s : S) (x : X) (y : Y), b (s • x) y = s • b x y)
    (ht : ∀ (t : Tᵐᵒᵖ) (x : X) (y : Y), b x (t • y) = t • b x y)
    (F : NonUnitalBimoduleHom S T (tensor X Y) Z)
    (hF : ∀ (x : X) (y : Y), F (tmul R X Y x y) = b x y),
    F = lift b hb hs ht := @lift_unique

example : ∀ {S : Type uS} {R : Type uR} [NonUnitalRing S] [NonUnitalRing R]
    {X : Type uX} [AddCommGroup X] [NonUnitalModule S X] [NonUnitalModule Rᵐᵒᵖ X]
    {X' : Type uX'} [AddCommGroup X'] [NonUnitalModule S X'] [NonUnitalModule Rᵐᵒᵖ X']
    {Y : Type uY} [AddCommGroup Y] [NonUnitalModule R Y]
    {Y' : Type uY'} [AddCommGroup Y'] [NonUnitalModule R Y']
    (hX : ActionsCommute S R X) (hX' : ActionsCommute S R X') (f : NonUnitalBimoduleHom S R X X') (g : NonUnitalModuleHom R Y Y'),
    @NonUnitalModuleHom S (Tensor R X Y) (Tensor R X' Y') _ _ _ (leftModule hX Y) (leftModule hX' Y') := @leftMap

example : ∀ {R : Type uR} {T : Type uT} [NonUnitalRing R] [NonUnitalRing T]
    {X : Type uX} [AddCommGroup X] [NonUnitalModule Rᵐᵒᵖ X]
    {X' : Type uX'} [AddCommGroup X'] [NonUnitalModule Rᵐᵒᵖ X']
    {Y : Type uY} [AddCommGroup Y] [NonUnitalModule R Y] [NonUnitalModule Tᵐᵒᵖ Y]
    {Y' : Type uY'} [AddCommGroup Y'] [NonUnitalModule R Y'] [NonUnitalModule Tᵐᵒᵖ Y']
    (hY : ActionsCommute R T Y) (hY' : ActionsCommute R T Y') (f : NonUnitalModuleHom Rᵐᵒᵖ X X') (g : NonUnitalBimoduleHom R T Y Y'),
    @NonUnitalModuleHom Tᵐᵒᵖ (Tensor R X Y) (Tensor R X' Y') _ _ _ (rightModule X hY) (rightModule X' hY') := @rightMap

example : ∀ {S : Type uS} {R : Type uR} [NonUnitalRing S] [NonUnitalRing R]
    {X : Type uX} [AddCommGroup X] [NonUnitalModule S X] [NonUnitalModule Rᵐᵒᵖ X]
    (hX : ActionsCommute S R X) {Y : Type uY} [AddCommGroup Y] [NonUnitalModule R Y]
    {Z : Type uZ} [AddCommGroup Z] [NonUnitalModule S Z]
    (b : X →+ Y →+ Z) (hb : NonUnitalModuleTensor.IsBalanced R b)
    (hs : ∀ (s : S) (x : X) (y : Y), b (s • x) y = s • b x y)
    (F : @NonUnitalModuleHom S (Tensor R X Y) Z _ _ _ (leftModule hX Y) _)
    (hF : ∀ (x : X) (y : Y), F (tmul R X Y x y) = b x y),
    F = leftLift hX b hb hs := @leftLift_unique

example : ∀ {R : Type uR} {T : Type uT} [NonUnitalRing R] [NonUnitalRing T]
    {X : Type uX} [AddCommGroup X] [NonUnitalModule Rᵐᵒᵖ X]
    {Y : Type uY} [AddCommGroup Y] [NonUnitalModule R Y] [NonUnitalModule Tᵐᵒᵖ Y]
    (hY : ActionsCommute R T Y) {Z : Type uZ} [AddCommGroup Z] [NonUnitalModule Tᵐᵒᵖ Z]
    (b : X →+ Y →+ Z) (hb : NonUnitalModuleTensor.IsBalanced R b)
    (ht : ∀ (t : Tᵐᵒᵖ) (x : X) (y : Y), b x (t • y) = t • b x y)
    (F : @NonUnitalModuleHom Tᵐᵒᵖ (Tensor R X Y) Z _ _ _ (rightModule X hY) _)
    (hF : ∀ (x : X) (y : Y), F (tmul R X Y x y) = b x y),
    F = rightLift hY b hb ht := @rightLift_unique

/-! Small rings, larger source factors and lift target, with unequal factor universes. -/

example : ∀ {S : Type 0} {R : Type 1} [NonUnitalRing S] [NonUnitalRing R]
    {X : Type 1} [AddCommGroup X] [NonUnitalModule S X] [NonUnitalModule Rᵐᵒᵖ X]
    (hX : ActionsCommute S R X) (Y : Type 0) [AddCommGroup Y] [NonUnitalModule R Y],
    S → (Tensor R X Y →+ Tensor R X Y) := @leftScalar

example : ∀ {S : Type 0} {R : Type 1} [NonUnitalRing S] [NonUnitalRing R]
    {X : Type 1} [AddCommGroup X] [NonUnitalModule S X] [NonUnitalModule Rᵐᵒᵖ X]
    (hX : ActionsCommute S R X) (Y : Type 0) [AddCommGroup Y] [NonUnitalModule R Y],
    NonUnitalModule S (Tensor R X Y) := @leftModule

example : ∀ {R : Type 1} {T : Type 0} [NonUnitalRing R] [NonUnitalRing T]
    (X : Type 1) [AddCommGroup X] [NonUnitalModule Rᵐᵒᵖ X]
    {Y : Type 0} [AddCommGroup Y] [NonUnitalModule R Y] [NonUnitalModule Tᵐᵒᵖ Y]
    (hY : ActionsCommute R T Y),
    Tᵐᵒᵖ → (Tensor R X Y →+ Tensor R X Y) := @rightScalar

example : ∀ {R : Type 1} {T : Type 0} [NonUnitalRing R] [NonUnitalRing T]
    (X : Type 1) [AddCommGroup X] [NonUnitalModule Rᵐᵒᵖ X]
    {Y : Type 0} [AddCommGroup Y] [NonUnitalModule R Y] [NonUnitalModule Tᵐᵒᵖ Y]
    (hY : ActionsCommute R T Y),
    NonUnitalModule Tᵐᵒᵖ (Tensor R X Y) := @rightModule

example : ∀ {S : Type 0} {R : Type 1} {T : Type 0}
    [NonUnitalRing S] [NonUnitalRing R] [NonUnitalRing T]
    {X : Type 1} [AddCommGroup X] [NonUnitalModule S X] [NonUnitalModule Rᵐᵒᵖ X]
    {Y : Type 0} [AddCommGroup Y] [NonUnitalModule R Y] [NonUnitalModule Tᵐᵒᵖ Y]
    (hX : ActionsCommute S R X) (hY : ActionsCommute R T Y),
    @ActionsCommute S T (Tensor R X Y) _ _ _ (leftModule hX Y) (rightModule X hY) := @actionsCommute

example : ∀ {S : Type 0} {R : Type 1} {T : Type 0}
    [NonUnitalRing S] [NonUnitalRing R] [NonUnitalRing T]
    {X : Type 1} [AddCommGroup X] [NonUnitalModule S X] [NonUnitalModule Rᵐᵒᵖ X]
    {Y : Type 0} [AddCommGroup Y] [NonUnitalModule R Y] [NonUnitalModule Tᵐᵒᵖ Y]
    (hX : ActionsCommute S R X) (hY : ActionsCommute R T Y),
    NonUnitalBimoduleCat.{0, 0, max 1 0} S T := @bimodule

example : ∀ {S : Type 0} {R : Type 1} {T : Type 0}
    [NonUnitalRing S] [NonUnitalRing R] [NonUnitalRing T] (X : NonUnitalBimoduleCat.{0, 1, 1} S R) (Y : NonUnitalBimoduleCat.{1, 0, 0} R T),
    NonUnitalBimoduleCat.{0, 0, max 1 0} S T := @tensor

example : ∀ {S : Type 0} {R : Type 1} {T : Type 0}
    [NonUnitalRing S] [NonUnitalRing R] [NonUnitalRing T]
    {X : NonUnitalBimoduleCat.{0, 1, 1} S R} {X' : NonUnitalBimoduleCat.{0, 1, 0} S R}
    {Y : NonUnitalBimoduleCat.{1, 0, 0} R T} {Y' : NonUnitalBimoduleCat.{1, 0, 1} R T},
    NonUnitalBimoduleHom S R X X' → NonUnitalBimoduleHom R T Y Y' →
      NonUnitalBimoduleHom S T (tensor X Y) (tensor X' Y') := @map

example : ∀ {S : Type 0} {R : Type 1} {T : Type 0}
    [NonUnitalRing S] [NonUnitalRing R] [NonUnitalRing T]
    {X : NonUnitalBimoduleCat.{0, 1, 1} S R} {X' : NonUnitalBimoduleCat.{0, 1, 0} S R} {X'' : NonUnitalBimoduleCat.{0, 1, 1} S R}
    {Y : NonUnitalBimoduleCat.{1, 0, 0} R T} {Y' : NonUnitalBimoduleCat.{1, 0, 1} R T} {Y'' : NonUnitalBimoduleCat.{1, 0, 0} R T} (f : NonUnitalBimoduleHom S R X X') (g : NonUnitalBimoduleHom R T Y Y')
    (f' : NonUnitalBimoduleHom S R X' X'') (g' : NonUnitalBimoduleHom R T Y' Y''),
    (map f' g').comp (map f g) = map (f'.comp f) (g'.comp g) := @map_comp

example : ∀ {S : Type 0} {R : Type 1} {T : Type 0}
    [NonUnitalRing S] [NonUnitalRing R] [NonUnitalRing T] (X₀ : NonUnitalBimoduleCat.{0, 1, 1} S R),
    NonUnitalBimoduleCat.{1, 0, 0} R T ⥤ NonUnitalBimoduleCat.{0, 0, max 1 0} S T := @tensorLeft

example : ∀ {S : Type 0} {R : Type 1} {T : Type 0}
    [NonUnitalRing S] [NonUnitalRing R] [NonUnitalRing T] (Y₀ : NonUnitalBimoduleCat.{1, 0, 0} R T),
    NonUnitalBimoduleCat.{0, 1, 1} S R ⥤ NonUnitalBimoduleCat.{0, 0, max 1 0} S T := @tensorRight

example : ∀ {S : Type 0} {R : Type 1} [NonUnitalRing S] [NonUnitalRing R]
    {X : Type 1} [AddCommGroup X] [NonUnitalModule S X] [NonUnitalModule Rᵐᵒᵖ X]
    (hX : ActionsCommute S R X) {Y : Type 0} [AddCommGroup Y] [NonUnitalModule R Y]
    {Z : Type 1} [AddCommGroup Z] [NonUnitalModule S Z]
    (b : X →+ Y →+ Z) (hb : NonUnitalModuleTensor.IsBalanced R b)
    (hs : ∀ (s : S) (x : X) (y : Y), b (s • x) y = s • b x y),
    @NonUnitalModuleHom S (Tensor R X Y) Z _ _ _ (leftModule hX Y) _ := @leftLift

example : ∀ {R : Type 1} {T : Type 0} [NonUnitalRing R] [NonUnitalRing T]
    {X : Type 1} [AddCommGroup X] [NonUnitalModule Rᵐᵒᵖ X]
    {Y : Type 0} [AddCommGroup Y] [NonUnitalModule R Y] [NonUnitalModule Tᵐᵒᵖ Y]
    (hY : ActionsCommute R T Y) {Z : Type 1} [AddCommGroup Z] [NonUnitalModule Tᵐᵒᵖ Z]
    (b : X →+ Y →+ Z) (hb : NonUnitalModuleTensor.IsBalanced R b)
    (ht : ∀ (t : Tᵐᵒᵖ) (x : X) (y : Y), b x (t • y) = t • b x y),
    @NonUnitalModuleHom Tᵐᵒᵖ (Tensor R X Y) Z _ _ _ (rightModule X hY) _ := @rightLift

example : ∀ {S : Type 0} {R : Type 1} {T : Type 0}
    [NonUnitalRing S] [NonUnitalRing R] [NonUnitalRing T]
    {X : NonUnitalBimoduleCat.{0, 1, 1} S R} {Y : NonUnitalBimoduleCat.{1, 0, 0} R T} {Z : NonUnitalBimoduleCat.{0, 0, 1} S T}
    (b : X →+ Y →+ Z) (hb : NonUnitalModuleTensor.IsBalanced R b)
    (hs : ∀ (s : S) (x : X) (y : Y), b (s • x) y = s • b x y)
    (ht : ∀ (t : Tᵐᵒᵖ) (x : X) (y : Y), b x (t • y) = t • b x y),
    NonUnitalBimoduleHom S T (tensor X Y) Z := @lift

example : ∀ {S : Type 0} {R : Type 1} [NonUnitalRing S] [NonUnitalRing R]
    {X : Type 1} [AddCommGroup X] [NonUnitalModule S X] [NonUnitalModule Rᵐᵒᵖ X]
    {X' : Type 0} [AddCommGroup X'] [NonUnitalModule S X'] [NonUnitalModule Rᵐᵒᵖ X']
    {Y : Type 0} [AddCommGroup Y] [NonUnitalModule R Y]
    {Y' : Type 1} [AddCommGroup Y'] [NonUnitalModule R Y']
    (hX : ActionsCommute S R X) (hX' : ActionsCommute S R X') (f : NonUnitalBimoduleHom S R X X') (g : NonUnitalModuleHom R Y Y'),
    @NonUnitalModuleHom S (Tensor R X Y) (Tensor R X' Y') _ _ _ (leftModule hX Y) (leftModule hX' Y') := @leftMap

example : ∀ {R : Type 1} {T : Type 0} [NonUnitalRing R] [NonUnitalRing T]
    {X : Type 1} [AddCommGroup X] [NonUnitalModule Rᵐᵒᵖ X]
    {X' : Type 0} [AddCommGroup X'] [NonUnitalModule Rᵐᵒᵖ X']
    {Y : Type 0} [AddCommGroup Y] [NonUnitalModule R Y] [NonUnitalModule Tᵐᵒᵖ Y]
    {Y' : Type 1} [AddCommGroup Y'] [NonUnitalModule R Y'] [NonUnitalModule Tᵐᵒᵖ Y']
    (hY : ActionsCommute R T Y) (hY' : ActionsCommute R T Y') (f : NonUnitalModuleHom Rᵐᵒᵖ X X') (g : NonUnitalBimoduleHom R T Y Y'),
    @NonUnitalModuleHom Tᵐᵒᵖ (Tensor R X Y) (Tensor R X' Y') _ _ _ (rightModule X hY) (rightModule X' hY') := @rightMap


/-! The reverse unequal assignments, including independent intermediate carriers. -/

example : ∀ {S : Type 1} {R : Type 0} [NonUnitalRing S] [NonUnitalRing R]
    {X : Type 0} [AddCommGroup X] [NonUnitalModule S X] [NonUnitalModule Rᵐᵒᵖ X]
    (hX : ActionsCommute S R X) (Y : Type 1) [AddCommGroup Y] [NonUnitalModule R Y],
    S → (Tensor R X Y →+ Tensor R X Y) := @leftScalar

example : ∀ {S : Type 1} {R : Type 0} [NonUnitalRing S] [NonUnitalRing R]
    {X : Type 0} [AddCommGroup X] [NonUnitalModule S X] [NonUnitalModule Rᵐᵒᵖ X]
    (hX : ActionsCommute S R X) (Y : Type 1) [AddCommGroup Y] [NonUnitalModule R Y],
    NonUnitalModule S (Tensor R X Y) := @leftModule

example : ∀ {R : Type 0} {T : Type 1} [NonUnitalRing R] [NonUnitalRing T]
    (X : Type 0) [AddCommGroup X] [NonUnitalModule Rᵐᵒᵖ X]
    {Y : Type 1} [AddCommGroup Y] [NonUnitalModule R Y] [NonUnitalModule Tᵐᵒᵖ Y]
    (hY : ActionsCommute R T Y),
    Tᵐᵒᵖ → (Tensor R X Y →+ Tensor R X Y) := @rightScalar

example : ∀ {R : Type 0} {T : Type 1} [NonUnitalRing R] [NonUnitalRing T]
    (X : Type 0) [AddCommGroup X] [NonUnitalModule Rᵐᵒᵖ X]
    {Y : Type 1} [AddCommGroup Y] [NonUnitalModule R Y] [NonUnitalModule Tᵐᵒᵖ Y]
    (hY : ActionsCommute R T Y),
    NonUnitalModule Tᵐᵒᵖ (Tensor R X Y) := @rightModule

example : ∀ {S : Type 1} {R : Type 0} {T : Type 1}
    [NonUnitalRing S] [NonUnitalRing R] [NonUnitalRing T]
    {X : Type 0} [AddCommGroup X] [NonUnitalModule S X] [NonUnitalModule Rᵐᵒᵖ X]
    {Y : Type 1} [AddCommGroup Y] [NonUnitalModule R Y] [NonUnitalModule Tᵐᵒᵖ Y]
    (hX : ActionsCommute S R X) (hY : ActionsCommute R T Y),
    @ActionsCommute S T (Tensor R X Y) _ _ _ (leftModule hX Y) (rightModule X hY) := @actionsCommute

example : ∀ {S : Type 1} {R : Type 0} {T : Type 1}
    [NonUnitalRing S] [NonUnitalRing R] [NonUnitalRing T]
    {X : Type 0} [AddCommGroup X] [NonUnitalModule S X] [NonUnitalModule Rᵐᵒᵖ X]
    {Y : Type 1} [AddCommGroup Y] [NonUnitalModule R Y] [NonUnitalModule Tᵐᵒᵖ Y]
    (hX : ActionsCommute S R X) (hY : ActionsCommute R T Y),
    NonUnitalBimoduleCat.{1, 1, max 0 1} S T := @bimodule

example : ∀ {S : Type 1} {R : Type 0} {T : Type 1}
    [NonUnitalRing S] [NonUnitalRing R] [NonUnitalRing T] (X : NonUnitalBimoduleCat.{1, 0, 0} S R) (Y : NonUnitalBimoduleCat.{0, 1, 1} R T),
    NonUnitalBimoduleCat.{1, 1, max 0 1} S T := @tensor

example : ∀ {S : Type 1} {R : Type 0} {T : Type 1}
    [NonUnitalRing S] [NonUnitalRing R] [NonUnitalRing T]
    {X : NonUnitalBimoduleCat.{1, 0, 0} S R} {X' : NonUnitalBimoduleCat.{1, 0, 1} S R}
    {Y : NonUnitalBimoduleCat.{0, 1, 1} R T} {Y' : NonUnitalBimoduleCat.{0, 1, 0} R T},
    NonUnitalBimoduleHom S R X X' → NonUnitalBimoduleHom R T Y Y' →
      NonUnitalBimoduleHom S T (tensor X Y) (tensor X' Y') := @map

example : ∀ {S : Type 1} {R : Type 0} {T : Type 1}
    [NonUnitalRing S] [NonUnitalRing R] [NonUnitalRing T]
    {X : NonUnitalBimoduleCat.{1, 0, 0} S R} {X' : NonUnitalBimoduleCat.{1, 0, 1} S R} {X'' : NonUnitalBimoduleCat.{1, 0, 0} S R}
    {Y : NonUnitalBimoduleCat.{0, 1, 1} R T} {Y' : NonUnitalBimoduleCat.{0, 1, 0} R T} {Y'' : NonUnitalBimoduleCat.{0, 1, 1} R T} (f : NonUnitalBimoduleHom S R X X') (g : NonUnitalBimoduleHom R T Y Y')
    (f' : NonUnitalBimoduleHom S R X' X'') (g' : NonUnitalBimoduleHom R T Y' Y''),
    (map f' g').comp (map f g) = map (f'.comp f) (g'.comp g) := @map_comp

example : ∀ {S : Type 1} {R : Type 0} {T : Type 1}
    [NonUnitalRing S] [NonUnitalRing R] [NonUnitalRing T] (X₀ : NonUnitalBimoduleCat.{1, 0, 0} S R),
    NonUnitalBimoduleCat.{0, 1, 1} R T ⥤ NonUnitalBimoduleCat.{1, 1, max 0 1} S T := @tensorLeft

example : ∀ {S : Type 1} {R : Type 0} {T : Type 1}
    [NonUnitalRing S] [NonUnitalRing R] [NonUnitalRing T] (Y₀ : NonUnitalBimoduleCat.{0, 1, 1} R T),
    NonUnitalBimoduleCat.{1, 0, 0} S R ⥤ NonUnitalBimoduleCat.{1, 1, max 0 1} S T := @tensorRight

example : ∀ {S : Type 1} {R : Type 0} [NonUnitalRing S] [NonUnitalRing R]
    {X : Type 0} [AddCommGroup X] [NonUnitalModule S X] [NonUnitalModule Rᵐᵒᵖ X]
    (hX : ActionsCommute S R X) {Y : Type 1} [AddCommGroup Y] [NonUnitalModule R Y]
    {Z : Type 0} [AddCommGroup Z] [NonUnitalModule S Z]
    (b : X →+ Y →+ Z) (hb : NonUnitalModuleTensor.IsBalanced R b)
    (hs : ∀ (s : S) (x : X) (y : Y), b (s • x) y = s • b x y),
    @NonUnitalModuleHom S (Tensor R X Y) Z _ _ _ (leftModule hX Y) _ := @leftLift

example : ∀ {R : Type 0} {T : Type 1} [NonUnitalRing R] [NonUnitalRing T]
    {X : Type 0} [AddCommGroup X] [NonUnitalModule Rᵐᵒᵖ X]
    {Y : Type 1} [AddCommGroup Y] [NonUnitalModule R Y] [NonUnitalModule Tᵐᵒᵖ Y]
    (hY : ActionsCommute R T Y) {Z : Type 0} [AddCommGroup Z] [NonUnitalModule Tᵐᵒᵖ Z]
    (b : X →+ Y →+ Z) (hb : NonUnitalModuleTensor.IsBalanced R b)
    (ht : ∀ (t : Tᵐᵒᵖ) (x : X) (y : Y), b x (t • y) = t • b x y),
    @NonUnitalModuleHom Tᵐᵒᵖ (Tensor R X Y) Z _ _ _ (rightModule X hY) _ := @rightLift

example : ∀ {S : Type 1} {R : Type 0} {T : Type 1}
    [NonUnitalRing S] [NonUnitalRing R] [NonUnitalRing T]
    {X : NonUnitalBimoduleCat.{1, 0, 0} S R} {Y : NonUnitalBimoduleCat.{0, 1, 1} R T} {Z : NonUnitalBimoduleCat.{1, 1, 0} S T}
    (b : X →+ Y →+ Z) (hb : NonUnitalModuleTensor.IsBalanced R b)
    (hs : ∀ (s : S) (x : X) (y : Y), b (s • x) y = s • b x y)
    (ht : ∀ (t : Tᵐᵒᵖ) (x : X) (y : Y), b x (t • y) = t • b x y),
    NonUnitalBimoduleHom S T (tensor X Y) Z := @lift

example : ∀ {S : Type 1} {R : Type 0} [NonUnitalRing S] [NonUnitalRing R]
    {X : Type 0} [AddCommGroup X] [NonUnitalModule S X] [NonUnitalModule Rᵐᵒᵖ X]
    {X' : Type 1} [AddCommGroup X'] [NonUnitalModule S X'] [NonUnitalModule Rᵐᵒᵖ X']
    {Y : Type 1} [AddCommGroup Y] [NonUnitalModule R Y]
    {Y' : Type 0} [AddCommGroup Y'] [NonUnitalModule R Y']
    (hX : ActionsCommute S R X) (hX' : ActionsCommute S R X') (f : NonUnitalBimoduleHom S R X X') (g : NonUnitalModuleHom R Y Y'),
    @NonUnitalModuleHom S (Tensor R X Y) (Tensor R X' Y') _ _ _ (leftModule hX Y) (leftModule hX' Y') := @leftMap

example : ∀ {R : Type 0} {T : Type 1} [NonUnitalRing R] [NonUnitalRing T]
    {X : Type 0} [AddCommGroup X] [NonUnitalModule Rᵐᵒᵖ X]
    {X' : Type 1} [AddCommGroup X'] [NonUnitalModule Rᵐᵒᵖ X']
    {Y : Type 1} [AddCommGroup Y] [NonUnitalModule R Y] [NonUnitalModule Tᵐᵒᵖ Y]
    {Y' : Type 0} [AddCommGroup Y'] [NonUnitalModule R Y'] [NonUnitalModule Tᵐᵒᵖ Y']
    (hY : ActionsCommute R T Y) (hY' : ActionsCommute R T Y') (f : NonUnitalModuleHom Rᵐᵒᵖ X X') (g : NonUnitalBimoduleHom R T Y Y'),
    @NonUnitalModuleHom Tᵐᵒᵖ (Tensor R X Y) (Tensor R X' Y') _ _ _ (rightModule X hY) (rightModule X' hY') := @rightMap


end Interfaces

/-! Named original structures survive competing ring, group and action instances. -/

section CompetingStructures

set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

variable (S : Type uS) (R : Type uR) (T : Type uT) (X : Type uX) (Y : Type uY)
  (s₀ : NonUnitalRing S) [s₁ : NonUnitalRing S]
  (r₀ : NonUnitalRing R) [r₁ : NonUnitalRing R]
  (t₀ : NonUnitalRing T) [t₁ : NonUnitalRing T]
  (gx₀ : AddCommGroup X) [gx₁ : AddCommGroup X]
  (gy₀ : AddCommGroup Y) [gy₁ : AddCommGroup Y]
  (xS₀ : @NonUnitalModule S X s₀ gx₀)
  (xR₀ : letI := r₀; @NonUnitalModule Rᵐᵒᵖ X _ gx₀)
  (yR₀ : @NonUnitalModule R Y r₀ gy₀)
  (yT₀ : letI := t₀; @NonUnitalModule Tᵐᵒᵖ Y _ gy₀)
  (hX : @ActionsCommute S R X s₀ r₀ gx₀ xS₀ xR₀)
  (hY : @ActionsCommute R T Y r₀ t₀ gy₀ yR₀ yT₀)
  [xS₁ : @NonUnitalModule S X s₁ gx₁]
  [xR₁ : letI := r₁; @NonUnitalModule Rᵐᵒᵖ X _ gx₁]
  [yR₁ : @NonUnitalModule R Y r₁ gy₁]
  [yT₁ : letI := t₁; @NonUnitalModule Tᵐᵒᵖ Y _ gy₁]

local notation "Q" => @Tensor R X Y r₀ gx₀ gy₀ xR₀ yR₀
local notation "GQ" => @NonUnitalModuleTensor.addCommGroup R X Y r₀ gx₀ gy₀ xR₀ yR₀
local notation "LQ" => @leftModule S R s₀ r₀ X gx₀ xS₀ xR₀ hX Y gy₀ yR₀
local notation "RQ" => @rightModule R T r₀ t₀ X gx₀ xR₀ Y gy₀ yR₀ yT₀ hY
local notation "BQ" => @bimodule S R T s₀ r₀ t₀ X gx₀ xS₀ xR₀ Y gy₀ yR₀ yT₀ hX hY

variable [gq₁ : AddCommGroup (@Tensor R X Y r₀ gx₀ gy₀ xR₀ yR₀)]
  [qS₁ : @NonUnitalModule S (@Tensor R X Y r₀ gx₀ gy₀ xR₀ yR₀) s₁ gq₁]
  [qT₁ : letI := t₁;
    @NonUnitalModule Tᵐᵒᵖ (@Tensor R X Y r₀ gx₀ gy₀ xR₀ yR₀) _ gq₁]

include s₁ r₁ t₁ gx₁ gy₁ xS₁ xR₁ yR₁ yT₁ gq₁ qS₁ qT₁

example : (inferInstance : NonUnitalRing S) = s₁ := rfl
example : (inferInstance : NonUnitalRing R) = r₁ := rfl
example : (inferInstance : NonUnitalRing T) = t₁ := rfl
example : (inferInstance : AddCommGroup X) = gx₁ := rfl
example : (inferInstance : AddCommGroup Y) = gy₁ := rfl
example : (inferInstance : NonUnitalModule S X) = xS₁ := rfl
example : (inferInstance : NonUnitalModule Rᵐᵒᵖ X) = xR₁ := rfl
example : (inferInstance : NonUnitalModule R Y) = yR₁ := rfl
example : (inferInstance : NonUnitalModule Tᵐᵒᵖ Y) = yT₁ := rfl
private theorem competingTensorGroup : (inferInstance : AddCommGroup Q) = gq₁ := rfl
private theorem competingTensorLeft : (inferInstance : @NonUnitalModule S Q s₁ gq₁) = qS₁ := rfl
private theorem competingTensorRight : (inferInstance :
    @NonUnitalModule Tᵐᵒᵖ Q (by letI := t₁; infer_instance) gq₁) = qT₁ := rfl

/-- The carrier is the quotient from the original balancing ring, groups and actions. -/
example : @NonUnitalBimoduleCat.carrier S T s₀ t₀ BQ = Q := rfl

/-- Its group is the published quotient group, even when another group on `Q` is active. -/
example : @NonUnitalBimoduleCat.isAddCommGroup S T s₀ t₀ BQ = GQ := rfl

example : @NonUnitalBimoduleCat.isLeftModule S T s₀ t₀ BQ = LQ := rfl

example : @NonUnitalBimoduleCat.isRightModule S T s₀ t₀ BQ = RQ := rfl

example : @ActionsCommute S T Q s₀ t₀ GQ LQ RQ :=
  @actionsCommute S R T s₀ r₀ t₀ X gx₀ xS₀ xR₀ Y gy₀ yR₀ yT₀ hX hY

/-- The complete scalar endomorphism uses the original action Hom and original identity. -/
example (s : S) :
    @NonUnitalModule.toEndHom S Q s₀ GQ LQ s =
      @NonUnitalModuleTensor.map R X Y r₀ gx₀ gy₀ xR₀ yR₀ X Y gx₀ gy₀ xR₀ yR₀
        (@ActionsCommute.leftActionHom S R X s₀ r₀ gx₀ xS₀ xR₀ hX s)
        (@NonUnitalModuleHom.id R Y r₀ gy₀ yR₀) := rfl

example (t : Tᵐᵒᵖ) :
    @NonUnitalModule.toEndHom Tᵐᵒᵖ Q (by letI := t₀; infer_instance) GQ RQ t =
      @NonUnitalModuleTensor.map R X Y r₀ gx₀ gy₀ xR₀ yR₀ X Y gx₀ gy₀ xR₀ yR₀
        (@NonUnitalModuleHom.id Rᵐᵒᵖ X (by letI := r₀; infer_instance) gx₀ xR₀)
        (@ActionsCommute.rightActionHom R T Y r₀ t₀ gy₀ yR₀ yT₀ hY t) := rfl

/-- The one-sided induced maps retain the named group and actions on both tensor carriers. -/
example : @NonUnitalModuleHom S Q Q s₀ GQ GQ LQ LQ :=
  @leftMap S R s₀ r₀ X gx₀ xS₀ xR₀ X gx₀ xS₀ xR₀
    Y gy₀ yR₀ Y gy₀ yR₀ hX hX
    (@NonUnitalBimoduleHom.id S R X s₀ r₀ gx₀ xS₀ xR₀)
    (@NonUnitalModuleHom.id R Y r₀ gy₀ yR₀)

example : @NonUnitalModuleHom Tᵐᵒᵖ Q Q (by letI := t₀; infer_instance) GQ GQ RQ RQ :=
  @rightMap R T r₀ t₀ X gx₀ xR₀ X gx₀ xR₀
    Y gy₀ yR₀ yT₀ Y gy₀ yR₀ yT₀ hY hY
    (@NonUnitalModuleHom.id Rᵐᵒᵖ X (by letI := r₀; infer_instance) gx₀ xR₀)
    (@NonUnitalBimoduleHom.id R T Y r₀ t₀ gy₀ yR₀ yT₀)

/-- The lifts of the canonical pairing use the original target group and named actions. -/
example : @NonUnitalModuleHom S Q Q s₀ GQ GQ LQ LQ :=
  @leftLift S R s₀ r₀ X gx₀ xS₀ xR₀ hX Y gy₀ yR₀ Q GQ LQ
    (@NonUnitalModuleTensor.biadditive R X Y r₀ gx₀ gy₀ xR₀ yR₀)
    (@NonUnitalModuleTensor.tmul_balanced R X Y r₀ gx₀ gy₀ xR₀ yR₀)
    (fun _ _ _ => rfl)

example : @NonUnitalModuleHom Tᵐᵒᵖ Q Q (by letI := t₀; infer_instance) GQ GQ RQ RQ :=
  @rightLift R T r₀ t₀ X gx₀ xR₀ Y gy₀ yR₀ yT₀ hY Q GQ RQ
    (@NonUnitalModuleTensor.biadditive R X Y r₀ gx₀ gy₀ xR₀ yR₀)
    (@NonUnitalModuleTensor.tmul_balanced R X Y r₀ gx₀ gy₀ xR₀ yR₀)
    (fun _ _ _ => rfl)

end CompetingStructures

/-! Subsingleton factors and zero remaining actions over arbitrary rings. -/

section BoundaryCases

variable {S : Type uS} {R : Type uR} {T : Type uT}
  [NonUnitalRing S] [NonUnitalRing R] [NonUnitalRing T]

example (X : NonUnitalBimoduleCat.{uS, uR, uX} S R)
    (Y : NonUnitalBimoduleCat.{uR, uT, uY} R T) [Subsingleton X] :
    Subsingleton (tensor X Y) := by
  have h : AddMonoidHom.id (tensor X Y) = 0 :=
    NonUnitalModuleTensor.hom_ext R fun x y => by
      change tmul R X Y x y = 0
      rw [Subsingleton.elim x 0, NonUnitalModuleTensor.zero_tmul]
  exact ⟨fun a b => (DFunLike.congr_fun h a).trans (DFunLike.congr_fun h b).symm⟩

example (X : NonUnitalBimoduleCat.{uS, uR, uX} S R)
    (Y : NonUnitalBimoduleCat.{uR, uT, uY} R T) [Subsingleton Y] :
    Subsingleton (tensor X Y) := by
  have h : AddMonoidHom.id (tensor X Y) = 0 :=
    NonUnitalModuleTensor.hom_ext R fun x y => by
      change tmul R X Y x y = 0
      rw [Subsingleton.elim y 0, NonUnitalModuleTensor.tmul_zero]
  exact ⟨fun a b => (DFunLike.congr_fun h a).trans (DFunLike.congr_fun h b).symm⟩

example {X : Type uX} [AddCommGroup X] [NonUnitalModule Rᵐᵒᵖ X]
    (Y : Type uY) [AddCommGroup Y] [NonUnitalModule R Y] (s : S) :
    @leftScalar S R _ _ X _ NonUnitalModule.zero _
      (@actionsCommute_zero_left S R X _ _ _ _) Y _ _ s = 0 := by
  apply NonUnitalModuleTensor.hom_ext R
  intro x y
  change tmul R X Y 0 y = 0
  exact NonUnitalModuleTensor.zero_tmul R X Y y

example (X : Type uX) [AddCommGroup X] [NonUnitalModule Rᵐᵒᵖ X]
    {Y : Type uY} [AddCommGroup Y] [NonUnitalModule R Y] (t : Tᵐᵒᵖ) :
    @rightScalar R T _ _ X _ _ Y _ _ NonUnitalModule.zero
      (@actionsCommute_zero_right R T Y _ _ _ _) t = 0 := by
  apply NonUnitalModuleTensor.hom_ext R
  intro x y
  change tmul R X Y x 0 = 0
  exact NonUnitalModuleTensor.tmul_zero R X Y x

/-- All three scalar rings may be zero rings, at independent universes. -/
example : NonUnitalBimoduleCat.{uS, uT, 0} PUnit.{uS + 1} PUnit.{uT + 1} :=
  tensor
    (@NonUnitalBimoduleCat.of PUnit.{uS + 1} PUnit.{uR + 1} _ _ ℤ _
      NonUnitalModule.zero NonUnitalModule.zero
      (@actionsCommute_zero_left PUnit PUnit ℤ _ _ _ NonUnitalModule.zero))
    (@NonUnitalBimoduleCat.of PUnit.{uR + 1} PUnit.{uT + 1} _ _ ℤ _
      NonUnitalModule.zero NonUnitalModule.zero
      (@actionsCommute_zero_left PUnit PUnit ℤ _ _ _ NonUnitalModule.zero))

end BoundaryCases

/-! Actual nonzero tensors with zero original balancing actions and zero remaining actions. -/

private abbrev zeroIntegerBimodule : NonUnitalBimoduleCat.{0, 0, 0} ℤ ℤ :=
  @NonUnitalBimoduleCat.of ℤ ℤ _ _ ℤ _ NonUnitalModule.zero NonUnitalModule.zero
    (@actionsCommute_zero_left ℤ ℤ ℤ _ _ _ NonUnitalModule.zero)

private def integerPairing : ℤ →+ ℤ →+ ℤ where
  toFun x :=
    { toFun y := x * y
      map_zero' := mul_zero x
      map_add' := mul_add x }
  map_zero' := AddMonoidHom.ext zero_mul
  map_add' x x' := AddMonoidHom.ext (fun y => add_mul x x' y)

section ZeroIntegerActions

local instance : NonUnitalModule ℤ ℤ := zeroIntegerBimodule.isLeftModule
local instance : NonUnitalModule ℤᵐᵒᵖ ℤ := zeroIntegerBimodule.isRightModule
local instance : NonUnitalModule ℤ (tensor zeroIntegerBimodule zeroIntegerBimodule) :=
  (tensor zeroIntegerBimodule zeroIntegerBimodule).isLeftModule
local instance : NonUnitalModule ℤᵐᵒᵖ (tensor zeroIntegerBimodule zeroIntegerBimodule) :=
  (tensor zeroIntegerBimodule zeroIntegerBimodule).isRightModule

private theorem zeroIntegerPairing_balanced :
    NonUnitalModuleTensor.IsBalanced ℤ
      (X := zeroIntegerBimodule) (Y := zeroIntegerBimodule) integerPairing := by
  intro a x y
  change (0 : ℤ) * y = x * 0
  rw [zero_mul, mul_zero]

private theorem zeroIntegerTensor_one_ne_zero :
    tmul ℤ zeroIntegerBimodule zeroIntegerBimodule 1 1 ≠ 0 := by
  intro h
  have h' := congrArg
    (NonUnitalModuleTensor.lift ℤ integerPairing zeroIntegerPairing_balanced) h
  change (1 : ℤ) = 0 at h'
  exact one_ne_zero h'

example : Nontrivial (tensor zeroIntegerBimodule zeroIntegerBimodule) :=
  ⟨⟨tmul ℤ zeroIntegerBimodule zeroIntegerBimodule 1 1, 0, zeroIntegerTensor_one_ne_zero⟩⟩

/-- Every whole remaining scalar endomorphism is zero on this nonzero tensor. -/
example (s : ℤ) :
    NonUnitalModule.toEndHom
      (tensor zeroIntegerBimodule zeroIntegerBimodule).isLeftModule s = 0 := by
  apply NonUnitalModuleTensor.hom_ext ℤ
  intro x y
  change tmul ℤ zeroIntegerBimodule zeroIntegerBimodule 0 y = 0
  exact NonUnitalModuleTensor.zero_tmul _ _ _ _

example (t : ℤᵐᵒᵖ) :
    NonUnitalModule.toEndHom
      (tensor zeroIntegerBimodule zeroIntegerBimodule).isRightModule t = 0 := by
  apply NonUnitalModuleTensor.hom_ext ℤ
  intro x y
  change tmul ℤ zeroIntegerBimodule zeroIntegerBimodule x 0 = 0
  exact NonUnitalModuleTensor.tmul_zero _ _ _ _

/-- The unit law actually fails, so the example does not impose `one_smul`. -/
example : ¬ ∀ z : tensor zeroIntegerBimodule zeroIntegerBimodule, (1 : ℤ) • z = z := by
  intro h
  have h' := h (tmul ℤ zeroIntegerBimodule zeroIntegerBimodule 1 1)
  change tmul ℤ zeroIntegerBimodule zeroIntegerBimodule 0 1 =
    tmul ℤ zeroIntegerBimodule zeroIntegerBimodule 1 1 at h'
  rw [NonUnitalModuleTensor.zero_tmul] at h'
  exact zeroIntegerTensor_one_ne_zero h'.symm

example : ¬ ∀ z : tensor zeroIntegerBimodule zeroIntegerBimodule, op (1 : ℤ) • z = z := by
  intro h
  have h' := h (tmul ℤ zeroIntegerBimodule zeroIntegerBimodule 1 1)
  change tmul ℤ zeroIntegerBimodule zeroIntegerBimodule 1 0 =
    tmul ℤ zeroIntegerBimodule zeroIntegerBimodule 1 1 at h'
  rw [NonUnitalModuleTensor.tmul_zero] at h'
  exact zeroIntegerTensor_one_ne_zero h'.symm

end ZeroIntegerActions

/-! The regular integer actions give the expected nonzero pure-tensor action. -/

section RegularIntegerActions

local instance : NonUnitalModule ℤ ℤ := (NonUnitalBimoduleCat.regular ℤ).isLeftModule
local instance : NonUnitalModule ℤᵐᵒᵖ ℤ := (NonUnitalBimoduleCat.regular ℤ).isRightModule
local instance : NonUnitalModule ℤ
    (tensor (NonUnitalBimoduleCat.regular ℤ) (NonUnitalBimoduleCat.regular ℤ)) :=
  (tensor (NonUnitalBimoduleCat.regular ℤ) (NonUnitalBimoduleCat.regular ℤ)).isLeftModule

private theorem regularIntegerPairing_balanced :
    NonUnitalModuleTensor.IsBalanced ℤ (X := NonUnitalBimoduleCat.regular ℤ)
      (Y := NonUnitalBimoduleCat.regular ℤ) integerPairing := by
  intro a x y
  change (x * a) * y = x * (a * y)
  exact mul_assoc x a y

private theorem regularIntegerTensor_two_ne_zero :
    tmul ℤ (NonUnitalBimoduleCat.regular ℤ) (NonUnitalBimoduleCat.regular ℤ) 2 1 ≠ 0 := by
  intro h
  have h' := congrArg
    (NonUnitalModuleTensor.lift ℤ integerPairing regularIntegerPairing_balanced) h
  change (2 : ℤ) = 0 at h'
  exact (by decide : (2 : ℤ) ≠ 0) h'

example :
    (2 : ℤ) •
        (tmul ℤ (NonUnitalBimoduleCat.regular ℤ) (NonUnitalBimoduleCat.regular ℤ) 1 1 :
          tensor (NonUnitalBimoduleCat.regular ℤ) (NonUnitalBimoduleCat.regular ℤ)) =
      tmul ℤ (NonUnitalBimoduleCat.regular ℤ) (NonUnitalBimoduleCat.regular ℤ) 2 1 := rfl

example :
    (2 : ℤ) •
        (tmul ℤ (NonUnitalBimoduleCat.regular ℤ) (NonUnitalBimoduleCat.regular ℤ) 1 1 :
          tensor (NonUnitalBimoduleCat.regular ℤ) (NonUnitalBimoduleCat.regular ℤ)) ≠ 0 :=
  regularIntegerTensor_two_ne_zero

end RegularIntegerActions

end Langlands.Algebra.NonUnitalBimoduleTensorChecks
