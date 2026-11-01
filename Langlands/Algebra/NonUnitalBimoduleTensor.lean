import Langlands.Algebra.NonUnitalModuleTensor
import Langlands.Algebra.NonUnitalBimodule

/-!
# Residual bimodule actions on balanced tensors of original nonunital modules

Renard (9 July 2026), I.2.2–I.2.3, printed pp.15–18/PDF21–24. For original
bimodules `_S X_R` and `_R Y_T`, the published balanced tensor `X ⊗_R Y` carries
the residual left `S`-action and right `T`-action, constructed separately from
the published tensor maps. They commute, are functorial, additive in each
factor, and the published universal lift is equivariant. No unit law or
nondegeneracy is imposed.
-/

set_option autoImplicit false

namespace Langlands.Algebra.NonUnitalBimoduleTensor

open CategoryTheory MulOpposite
open Langlands.Algebra.NonUnitalModuleTensor (Tensor tmul hom_ext)

universe uS uR uT uX uY uZ uX' uY' uX'' uY''

/-! ## The left action, from `_S X_R` and a left `R`-module `Y` alone -/

section Left

variable {S : Type uS} {R : Type uR} [NonUnitalRing S] [NonUnitalRing R]
  {X : Type uX} [AddCommGroup X] [NonUnitalModule S X] [NonUnitalModule Rᵐᵒᵖ X]
  (hX : ActionsCommute S R X) (Y : Type uY) [AddCommGroup Y] [NonUnitalModule R Y]

/-- The whole left scalar endomorphism: the published tensor map of the right `R`-linear
action of `s` on `X` and the original identity of `Y`. -/
def leftScalar (s : S) : Tensor R X Y →+ Tensor R X Y :=
  NonUnitalModuleTensor.map R (hX.leftActionHom s) (NonUnitalModuleHom.id R Y)

theorem leftScalar_def (s : S) :
    leftScalar hX Y s =
      NonUnitalModuleTensor.map R (hX.leftActionHom s) (NonUnitalModuleHom.id R Y) := rfl

@[simp] theorem leftScalar_tmul (s : S) (x : X) (y : Y) :
    leftScalar hX Y s (tmul R X Y x y) = tmul R X Y (s • x) y := rfl

theorem leftScalar_zero : leftScalar hX Y 0 = 0 :=
  hom_ext R fun x y => by
    change tmul R X Y ((0 : S) • x) y = 0
    rw [NonUnitalModule.zero_smul, NonUnitalModuleTensor.zero_tmul]

theorem leftScalar_add (s s' : S) :
    leftScalar hX Y (s + s') = leftScalar hX Y s + leftScalar hX Y s' :=
  hom_ext R fun x y => by
    change tmul R X Y ((s + s') • x) y = tmul R X Y (s • x) y + tmul R X Y (s' • x) y
    rw [NonUnitalModule.add_smul, NonUnitalModuleTensor.add_tmul]

theorem leftScalar_mul (s s' : S) :
    leftScalar hX Y (s * s') = (leftScalar hX Y s).comp (leftScalar hX Y s') :=
  hom_ext R fun x y => by
    change tmul R X Y ((s * s') • x) y = tmul R X Y (s • s' • x) y
    rw [mul_smul]

/-- The named original left `S`-module on the published tensor carrier and group. -/
@[instance_reducible] def leftModule : NonUnitalModule S (Tensor R X Y) where
  smul s t := leftScalar hX Y s t
  smul_zero s := map_zero (leftScalar hX Y s)
  smul_add s := map_add (leftScalar hX Y s)
  mul_smul s s' t := DFunLike.congr_fun (leftScalar_mul hX Y s s') t
  add_smul s s' t := DFunLike.congr_fun (leftScalar_add hX Y s s') t
  zero_smul t := DFunLike.congr_fun (leftScalar_zero hX Y) t

/-- The pure-tensor formula `s • (x ⊗ y) = (s • x) ⊗ y`. -/
theorem leftModule_smul_tmul (s : S) (x : X) (y : Y) :
    letI := leftModule hX Y
    s • tmul R X Y x y = tmul R X Y (s • x) y := rfl

/-- The entire additive endomorphism of `s` is the published tensor map. -/
theorem toEndHom_leftModule (s : S) :
    NonUnitalModule.toEndHom (leftModule hX Y) s =
      NonUnitalModuleTensor.map R (hX.leftActionHom s) (NonUnitalModuleHom.id R Y) := rfl

end Left

/-! ## The right action, from a right `R`-module `X` and `_R Y_T` alone -/

section Right

variable {R : Type uR} {T : Type uT} [NonUnitalRing R] [NonUnitalRing T]
  (X : Type uX) [AddCommGroup X] [NonUnitalModule Rᵐᵒᵖ X]
  {Y : Type uY} [AddCommGroup Y] [NonUnitalModule R Y] [NonUnitalModule Tᵐᵒᵖ Y]
  (hY : ActionsCommute R T Y)

/-- The whole right scalar endomorphism: the published tensor map of the original identity
of `X` and the left `R`-linear action of `t : Tᵐᵒᵖ` on `Y`. -/
def rightScalar (t : Tᵐᵒᵖ) : Tensor R X Y →+ Tensor R X Y :=
  NonUnitalModuleTensor.map R (NonUnitalModuleHom.id Rᵐᵒᵖ X) (hY.rightActionHom t)

theorem rightScalar_def (t : Tᵐᵒᵖ) :
    rightScalar X hY t =
      NonUnitalModuleTensor.map R (NonUnitalModuleHom.id Rᵐᵒᵖ X) (hY.rightActionHom t) := rfl

@[simp] theorem rightScalar_tmul (t : Tᵐᵒᵖ) (x : X) (y : Y) :
    rightScalar X hY t (tmul R X Y x y) = tmul R X Y x (t • y) := rfl

theorem rightScalar_zero : rightScalar X hY 0 = 0 :=
  hom_ext R fun x y => by
    change tmul R X Y x ((0 : Tᵐᵒᵖ) • y) = 0
    rw [NonUnitalModule.zero_smul, NonUnitalModuleTensor.tmul_zero]

theorem rightScalar_add (t t' : Tᵐᵒᵖ) :
    rightScalar X hY (t + t') = rightScalar X hY t + rightScalar X hY t' :=
  hom_ext R fun x y => by
    change tmul R X Y x ((t + t') • y) = tmul R X Y x (t • y) + tmul R X Y x (t' • y)
    rw [NonUnitalModule.add_smul, NonUnitalModuleTensor.tmul_add]

theorem rightScalar_mul (t t' : Tᵐᵒᵖ) :
    rightScalar X hY (t * t') = (rightScalar X hY t).comp (rightScalar X hY t') :=
  hom_ext R fun x y => by
    change tmul R X Y x ((t * t') • y) = tmul R X Y x (t • t' • y)
    rw [mul_smul]

/-- In right-action notation, multiplication in `T` composes in the reverse order. -/
theorem rightScalar_op_mul (t t' : T) :
    rightScalar X hY (op (t * t')) = (rightScalar X hY (op t')).comp (rightScalar X hY (op t)) := by
  rw [op_mul, rightScalar_mul]

/-- The named original right `T`-module, a left `Tᵐᵒᵖ`-module, on the published tensor. -/
@[instance_reducible] def rightModule : NonUnitalModule Tᵐᵒᵖ (Tensor R X Y) where
  smul t z := rightScalar X hY t z
  smul_zero t := map_zero (rightScalar X hY t)
  smul_add t := map_add (rightScalar X hY t)
  mul_smul t t' z := DFunLike.congr_fun (rightScalar_mul X hY t t') z
  add_smul t t' z := DFunLike.congr_fun (rightScalar_add X hY t t') z
  zero_smul z := DFunLike.congr_fun (rightScalar_zero X hY) z

/-- The pure-tensor formula for an opposite scalar `t : Tᵐᵒᵖ`. -/
theorem rightModule_smul_tmul (t : Tᵐᵒᵖ) (x : X) (y : Y) :
    letI := rightModule X hY
    t • tmul R X Y x y = tmul R X Y x (t • y) := rfl

/-- The pure-tensor formula `op t • (x ⊗ y) = x ⊗ (op t • y)`. -/
theorem rightModule_op_smul_tmul (t : T) (x : X) (y : Y) :
    letI := rightModule X hY
    op t • tmul R X Y x y = tmul R X Y x (op t • y) := rfl

/-- The entire additive endomorphism of `t` is the published tensor map. -/
theorem toEndHom_rightModule (t : Tᵐᵒᵖ) :
    NonUnitalModule.toEndHom (rightModule X hY) t =
      NonUnitalModuleTensor.map R (NonUnitalModuleHom.id Rᵐᵒᵖ X) (hY.rightActionHom t) := rfl

end Right

/-! ## Commutation and the bundled tensor bimodule -/

section Both

variable {S : Type uS} {R : Type uR} {T : Type uT}
  [NonUnitalRing S] [NonUnitalRing R] [NonUnitalRing T]
  {X : Type uX} [AddCommGroup X] [NonUnitalModule S X] [NonUnitalModule Rᵐᵒᵖ X]
  {Y : Type uY} [AddCommGroup Y] [NonUnitalModule R Y] [NonUnitalModule Tᵐᵒᵖ Y]
  (hX : ActionsCommute S R X) (hY : ActionsCommute R T Y)

/-- The two whole scalar endomorphisms commute. -/
theorem leftScalar_comp_rightScalar (s : S) (t : Tᵐᵒᵖ) :
    (leftScalar hX Y s).comp (rightScalar X hY t) =
      (rightScalar X hY t).comp (leftScalar hX Y s) :=
  hom_ext R fun _ _ => rfl

/-- The named residual actions commute. -/
theorem actionsCommute :
    @ActionsCommute S T (Tensor R X Y) _ _ _ (leftModule hX Y) (rightModule X hY) :=
  fun s t z => DFunLike.congr_fun (leftScalar_comp_rightScalar hX hY s (op t)) z

/-- The tensor with both residual actions, in the published bimodule category. -/
def bimodule : NonUnitalBimoduleCat.{uS, uT, max uX uY} S T :=
  @NonUnitalBimoduleCat.of S T _ _ (Tensor R X Y) _ (leftModule hX Y) (rightModule X hY)
    (actionsCommute hX hY)

theorem bimodule_carrier : (bimodule hX hY).carrier = Tensor R X Y := rfl

theorem bimodule_isAddCommGroup :
    (bimodule hX hY).isAddCommGroup = NonUnitalModuleTensor.addCommGroup R X Y := rfl

theorem bimodule_isLeftModule : (bimodule hX hY).isLeftModule = leftModule hX Y := rfl

theorem bimodule_isRightModule : (bimodule hX hY).isRightModule = rightModule X hY := rfl

/-- The whole left scalar map of the bundled tensor. -/
theorem toEndHom_bimodule_left (s : S) :
    NonUnitalModule.toEndHom (bimodule hX hY).isLeftModule s =
      NonUnitalModuleTensor.map R (hX.leftActionHom s) (NonUnitalModuleHom.id R Y) := rfl

/-- The whole right scalar map of the bundled tensor. -/
theorem toEndHom_bimodule_right (t : Tᵐᵒᵖ) :
    NonUnitalModule.toEndHom (bimodule hX hY).isRightModule t =
      NonUnitalModuleTensor.map R (NonUnitalModuleHom.id Rᵐᵒᵖ X) (hY.rightActionHom t) := rfl

theorem bimodule_smul_tmul (s : S) (x : X) (y : Y) :
    @HSMul.hSMul S (bimodule hX hY) (bimodule hX hY) _ s (tmul R X Y x y) =
      tmul R X Y (s • x) y := rfl

theorem bimodule_op_smul_tmul (t : T) (x : X) (y : Y) :
    @HSMul.hSMul Tᵐᵒᵖ (bimodule hX hY) (bimodule hX hY) _ (op t) (tmul R X Y x y) =
      tmul R X Y x (op t • y) := rfl

end Both

/-- The tensor of two bundled original bimodules. -/
abbrev tensor {S : Type uS} {R : Type uR} {T : Type uT}
    [NonUnitalRing S] [NonUnitalRing R] [NonUnitalRing T]
    (X : NonUnitalBimoduleCat.{uS, uR, uX} S R) (Y : NonUnitalBimoduleCat.{uR, uT, uY} R T) :
    NonUnitalBimoduleCat.{uS, uT, max uX uY} S T :=
  bimodule X.actionsCommute Y.actionsCommute

/-! ## Induced maps -/

section OneSidedMaps

variable {S : Type uS} {R : Type uR} {T : Type uT}
  [NonUnitalRing S] [NonUnitalRing R] [NonUnitalRing T]

section LeftMap

variable {X : Type uX} [AddCommGroup X] [NonUnitalModule S X] [NonUnitalModule Rᵐᵒᵖ X]
  {X' : Type uX'} [AddCommGroup X'] [NonUnitalModule S X'] [NonUnitalModule Rᵐᵒᵖ X']
  {Y : Type uY} [AddCommGroup Y] [NonUnitalModule R Y]
  {Y' : Type uY'} [AddCommGroup Y'] [NonUnitalModule R Y']
  (hX : ActionsCommute S R X) (hX' : ActionsCommute S R X')

theorem map_comp_leftScalar (f : NonUnitalBimoduleHom S R X X') (g : NonUnitalModuleHom R Y Y')
    (s : S) :
    (NonUnitalModuleTensor.map R f.toRightHom g).comp (leftScalar hX Y s) =
      (leftScalar hX' Y' s).comp (NonUnitalModuleTensor.map R f.toRightHom g) :=
  hom_ext R fun x y => by
    change tmul R X' Y' (f (s • x)) (g y) = tmul R X' Y' (s • f x) (g y)
    rw [f.map_smul_left]

/-- The published tensor map of an `S–R` intertwiner and a left `R`-linear map is `S`-linear. -/
def leftMap (f : NonUnitalBimoduleHom S R X X') (g : NonUnitalModuleHom R Y Y') :
    @NonUnitalModuleHom S (Tensor R X Y) (Tensor R X' Y') _ _ _ (leftModule hX Y)
      (leftModule hX' Y') :=
  @NonUnitalModuleHom.mk S (Tensor R X Y) (Tensor R X' Y') _ _ _ (leftModule hX Y)
    (leftModule hX' Y') (NonUnitalModuleTensor.map R f.toRightHom g)
    (fun s z => DFunLike.congr_fun (map_comp_leftScalar hX hX' f g s) z)

/-- The complete additive map is the published tensor map. -/
theorem leftMap_toAddMonoidHom (f : NonUnitalBimoduleHom S R X X')
    (g : NonUnitalModuleHom R Y Y') :
    letI := leftModule hX Y
    letI := leftModule hX' Y'
    (leftMap hX hX' f g).toAddMonoidHom = NonUnitalModuleTensor.map R f.toRightHom g := rfl

@[simp] theorem leftMap_tmul (f : NonUnitalBimoduleHom S R X X') (g : NonUnitalModuleHom R Y Y')
    (x : X) (y : Y) :
    letI := leftModule hX Y
    letI := leftModule hX' Y'
    leftMap hX hX' f g (tmul R X Y x y) = tmul R X' Y' (f x) (g y) := rfl

end LeftMap

section RightMap

variable {X : Type uX} [AddCommGroup X] [NonUnitalModule Rᵐᵒᵖ X]
  {X' : Type uX'} [AddCommGroup X'] [NonUnitalModule Rᵐᵒᵖ X']
  {Y : Type uY} [AddCommGroup Y] [NonUnitalModule R Y] [NonUnitalModule Tᵐᵒᵖ Y]
  {Y' : Type uY'} [AddCommGroup Y'] [NonUnitalModule R Y'] [NonUnitalModule Tᵐᵒᵖ Y']
  (hY : ActionsCommute R T Y) (hY' : ActionsCommute R T Y')

theorem map_comp_rightScalar (f : NonUnitalModuleHom Rᵐᵒᵖ X X')
    (g : NonUnitalBimoduleHom R T Y Y') (t : Tᵐᵒᵖ) :
    (NonUnitalModuleTensor.map R f g.toLeftHom).comp (rightScalar X hY t) =
      (rightScalar X' hY' t).comp (NonUnitalModuleTensor.map R f g.toLeftHom) :=
  hom_ext R fun x y => by
    change tmul R X' Y' (f x) (g (t • y)) = tmul R X' Y' (f x) (t • g y)
    rw [g.map_smul_right]

/-- The published tensor map of a right `R`-linear map and an `R–T` intertwiner is right
`T`-linear. -/
def rightMap (f : NonUnitalModuleHom Rᵐᵒᵖ X X') (g : NonUnitalBimoduleHom R T Y Y') :
    @NonUnitalModuleHom Tᵐᵒᵖ (Tensor R X Y) (Tensor R X' Y') _ _ _ (rightModule X hY)
      (rightModule X' hY') :=
  @NonUnitalModuleHom.mk Tᵐᵒᵖ (Tensor R X Y) (Tensor R X' Y') _ _ _ (rightModule X hY)
    (rightModule X' hY') (NonUnitalModuleTensor.map R f g.toLeftHom)
    (fun t z => DFunLike.congr_fun (map_comp_rightScalar hY hY' f g t) z)

/-- The complete additive map is the published tensor map. -/
theorem rightMap_toAddMonoidHom (f : NonUnitalModuleHom Rᵐᵒᵖ X X')
    (g : NonUnitalBimoduleHom R T Y Y') :
    letI := rightModule X hY
    letI := rightModule X' hY'
    (rightMap hY hY' f g).toAddMonoidHom = NonUnitalModuleTensor.map R f g.toLeftHom := rfl

@[simp] theorem rightMap_tmul (f : NonUnitalModuleHom Rᵐᵒᵖ X X')
    (g : NonUnitalBimoduleHom R T Y Y') (x : X) (y : Y) :
    letI := rightModule X hY
    letI := rightModule X' hY'
    rightMap hY hY' f g (tmul R X Y x y) = tmul R X' Y' (f x) (g y) := rfl

end RightMap

end OneSidedMaps

section BundledMaps

variable {S : Type uS} {R : Type uR} {T : Type uT}
  [NonUnitalRing S] [NonUnitalRing R] [NonUnitalRing T]
  {X : NonUnitalBimoduleCat.{uS, uR, uX} S R} {X' : NonUnitalBimoduleCat.{uS, uR, uX'} S R}
  {X'' : NonUnitalBimoduleCat.{uS, uR, uX''} S R}
  {Y : NonUnitalBimoduleCat.{uR, uT, uY} R T} {Y' : NonUnitalBimoduleCat.{uR, uT, uY'} R T}
  {Y'' : NonUnitalBimoduleCat.{uR, uT, uY''} R T}

/-- Bimodule maps out of the bundled tensor are determined by their pure-tensor values. -/
theorem bimoduleHom_ext {N : Type uZ} [AddCommGroup N] [NonUnitalModule S N]
    [NonUnitalModule Tᵐᵒᵖ N] {F G : NonUnitalBimoduleHom S T (tensor X Y) N}
    (h : ∀ (x : X) (y : Y), F (tmul R X Y x y) = G (tmul R X Y x y)) : F = G :=
  Subtype.ext (hom_ext R (X := X) (Y := Y) h)

/-- The tensor of two original bimodule intertwiners: the published tensor map of their
right and left projections, as an actual `S–T` intertwiner. -/
def map (f : NonUnitalBimoduleHom S R X X') (g : NonUnitalBimoduleHom R T Y Y') :
    NonUnitalBimoduleHom S T (tensor X Y) (tensor X' Y') :=
  ⟨NonUnitalModuleTensor.map R f.toRightHom g.toLeftHom,
    fun s z => DFunLike.congr_fun
      (map_comp_leftScalar X.actionsCommute X'.actionsCommute f g.toLeftHom s) z,
    fun t z => DFunLike.congr_fun
      (map_comp_rightScalar Y.actionsCommute Y'.actionsCommute f.toRightHom g t) z⟩

@[simp] theorem map_tmul (f : NonUnitalBimoduleHom S R X X') (g : NonUnitalBimoduleHom R T Y Y')
    (x : X) (y : Y) : map f g (tmul R X Y x y) = tmul R X' Y' (f x) (g y) := rfl

/-- The complete additive map is the published tensor map. -/
theorem map_val (f : NonUnitalBimoduleHom S R X X') (g : NonUnitalBimoduleHom R T Y Y') :
    (map f g).val = NonUnitalModuleTensor.map R f.toRightHom g.toLeftHom := rfl

/-- The complete left projection is the one-sided `S`-linear tensor map. -/
theorem map_toLeftHom (f : NonUnitalBimoduleHom S R X X') (g : NonUnitalBimoduleHom R T Y Y') :
    (map f g).toLeftHom = leftMap X.actionsCommute X'.actionsCommute f g.toLeftHom := rfl

/-- The complete right projection is the one-sided right `T`-linear tensor map. -/
theorem map_toRightHom (f : NonUnitalBimoduleHom S R X X') (g : NonUnitalBimoduleHom R T Y Y') :
    (map f g).toRightHom = rightMap Y.actionsCommute Y'.actionsCommute f.toRightHom g := rfl

theorem map_id :
    map (NonUnitalBimoduleHom.id S R X) (NonUnitalBimoduleHom.id R T Y) =
      NonUnitalBimoduleHom.id S T (tensor X Y) :=
  Subtype.ext (NonUnitalModuleTensor.map_id R)

theorem map_comp (f : NonUnitalBimoduleHom S R X X') (g : NonUnitalBimoduleHom R T Y Y')
    (f' : NonUnitalBimoduleHom S R X' X'') (g' : NonUnitalBimoduleHom R T Y' Y'') :
    (map f' g').comp (map f g) = map (f'.comp f) (g'.comp g) :=
  Subtype.ext
    (NonUnitalModuleTensor.map_comp R f.toRightHom g.toLeftHom f'.toRightHom g'.toLeftHom)

theorem map_zero_left (g : NonUnitalBimoduleHom R T Y Y') :
    map (0 : NonUnitalBimoduleHom S R X X') g = 0 :=
  bimoduleHom_ext fun _ y => NonUnitalModuleTensor.zero_tmul R X' Y' (g y)

theorem map_zero_right (f : NonUnitalBimoduleHom S R X X') :
    map f (0 : NonUnitalBimoduleHom R T Y Y') = 0 :=
  bimoduleHom_ext fun x _ => NonUnitalModuleTensor.tmul_zero R X' Y' (f x)

/-- Additivity in the left intertwiner, with the right one fixed. -/
theorem map_add_left (f₁ f₂ : NonUnitalBimoduleHom S R X X') (g : NonUnitalBimoduleHom R T Y Y') :
    map (f₁ + f₂) g = map f₁ g + map f₂ g :=
  bimoduleHom_ext fun x y => NonUnitalModuleTensor.add_tmul R X' Y' (f₁ x) (f₂ x) (g y)

/-- Additivity in the right intertwiner, with the left one fixed. -/
theorem map_add_right (f : NonUnitalBimoduleHom S R X X') (g₁ g₂ : NonUnitalBimoduleHom R T Y Y') :
    map f (g₁ + g₂) = map f g₁ + map f g₂ :=
  bimoduleHom_ext fun x y => NonUnitalModuleTensor.tmul_add R X' Y' (f x) (g₁ y) (g₂ y)

/-- The tensor map as an additive map of the left intertwiner. -/
def mapLeftAddHom (g : NonUnitalBimoduleHom R T Y Y') :
    NonUnitalBimoduleHom S R X X' →+ NonUnitalBimoduleHom S T (tensor X Y) (tensor X' Y') where
  toFun f := map f g
  map_zero' := map_zero_left g
  map_add' f₁ f₂ := map_add_left f₁ f₂ g

/-- The tensor map as an additive map of the right intertwiner. -/
def mapRightAddHom (f : NonUnitalBimoduleHom S R X X') :
    NonUnitalBimoduleHom R T Y Y' →+ NonUnitalBimoduleHom S T (tensor X Y) (tensor X' Y') where
  toFun g := map f g
  map_zero' := map_zero_right f
  map_add' g₁ g₂ := map_add_right f g₁ g₂

@[simp] theorem mapLeftAddHom_apply (g : NonUnitalBimoduleHom R T Y Y')
    (f : NonUnitalBimoduleHom S R X X') : mapLeftAddHom g f = map f g := rfl

@[simp] theorem mapRightAddHom_apply (f : NonUnitalBimoduleHom S R X X')
    (g : NonUnitalBimoduleHom R T Y Y') : mapRightAddHom f g = map f g := rfl

end BundledMaps

/-! ## The fixed-factor additive functors -/

section Functors

variable {S : Type uS} {R : Type uR} {T : Type uT}
  [NonUnitalRing S] [NonUnitalRing R] [NonUnitalRing T]

/-- Fixed left factor: `Y ↦ X₀ ⊗_R Y` and `g ↦ id ⊗ g`. -/
def tensorLeft (X₀ : NonUnitalBimoduleCat.{uS, uR, uX} S R) :
    NonUnitalBimoduleCat.{uR, uT, uY} R T ⥤ NonUnitalBimoduleCat.{uS, uT, max uX uY} S T where
  obj Y := tensor X₀ Y
  map g := map (NonUnitalBimoduleHom.id S R X₀) g
  map_id _ := map_id
  map_comp g g' := (map_comp (NonUnitalBimoduleHom.id S R X₀) g
    (NonUnitalBimoduleHom.id S R X₀) g').symm

/-- Fixed right factor: `X ↦ X ⊗_R Y₀` and `f ↦ f ⊗ id`. -/
def tensorRight (Y₀ : NonUnitalBimoduleCat.{uR, uT, uY} R T) :
    NonUnitalBimoduleCat.{uS, uR, uX} S R ⥤ NonUnitalBimoduleCat.{uS, uT, max uX uY} S T where
  obj X := tensor X Y₀
  map f := map f (NonUnitalBimoduleHom.id R T Y₀)
  map_id _ := map_id
  map_comp f f' := (map_comp f (NonUnitalBimoduleHom.id R T Y₀) f'
    (NonUnitalBimoduleHom.id R T Y₀)).symm

variable (X₀ : NonUnitalBimoduleCat.{uS, uR, uX} S R) (Y₀ : NonUnitalBimoduleCat.{uR, uT, uY} R T)

instance tensorLeft_additive :
    (tensorLeft X₀ : NonUnitalBimoduleCat.{uR, uT, uY} R T ⥤ _).Additive where
  map_add {_ _ g g'} := map_add_right (NonUnitalBimoduleHom.id S R X₀) g g'

instance tensorRight_additive :
    (tensorRight Y₀ : NonUnitalBimoduleCat.{uS, uR, uX} S R ⥤ _).Additive where
  map_add {_ _ f f'} := map_add_left f f' (NonUnitalBimoduleHom.id R T Y₀)

theorem tensorLeft_obj (Y : NonUnitalBimoduleCat.{uR, uT, uY} R T) :
    (tensorLeft X₀).obj Y = tensor X₀ Y := rfl

theorem tensorRight_obj (X : NonUnitalBimoduleCat.{uS, uR, uX} S R) :
    (tensorRight Y₀).obj X = tensor X Y₀ := rfl

theorem tensorLeft_obj_carrier (Y : NonUnitalBimoduleCat.{uR, uT, uY} R T) :
    ((tensorLeft X₀).obj Y).carrier = Tensor R X₀ Y := rfl

theorem tensorRight_obj_carrier (X : NonUnitalBimoduleCat.{uS, uR, uX} S R) :
    ((tensorRight Y₀).obj X).carrier = Tensor R X Y₀ := rfl

theorem tensorLeft_map {Y Y' : NonUnitalBimoduleCat.{uR, uT, uY} R T} (g : Y ⟶ Y') :
    (tensorLeft X₀).map g = map (NonUnitalBimoduleHom.id S R X₀) g := rfl

theorem tensorRight_map {X X' : NonUnitalBimoduleCat.{uS, uR, uX} S R} (f : X ⟶ X') :
    (tensorRight Y₀).map f = map f (NonUnitalBimoduleHom.id R T Y₀) := rfl

/-- The complete additive map of `(tensorLeft X₀).map g` is the published tensor map. -/
theorem tensorLeft_map_val {Y Y' : NonUnitalBimoduleCat.{uR, uT, uY} R T} (g : Y ⟶ Y') :
    Subtype.val ((tensorLeft X₀).map g) =
      NonUnitalModuleTensor.map R (NonUnitalModuleHom.id Rᵐᵒᵖ X₀)
        (NonUnitalBimoduleHom.toLeftHom g) := rfl

/-- The complete additive map of `(tensorRight Y₀).map f` is the published tensor map. -/
theorem tensorRight_map_val {X X' : NonUnitalBimoduleCat.{uS, uR, uX} S R} (f : X ⟶ X') :
    Subtype.val ((tensorRight Y₀).map f) =
      NonUnitalModuleTensor.map R (NonUnitalBimoduleHom.toRightHom f)
        (NonUnitalModuleHom.id R Y₀) := rfl

/-- On Hom groups the fixed-left-factor functor is the additive map of the right intertwiner. -/
theorem tensorLeft_mapAddHom (Y Y' : NonUnitalBimoduleCat.{uR, uT, uY} R T) :
    (tensorLeft X₀).mapAddHom (X := Y) (Y := Y') =
      mapRightAddHom (NonUnitalBimoduleHom.id S R X₀) := rfl

/-- On Hom groups the fixed-right-factor functor is the additive map of the left intertwiner. -/
theorem tensorRight_mapAddHom (X X' : NonUnitalBimoduleCat.{uS, uR, uX} S R) :
    (tensorRight Y₀).mapAddHom (X := X) (Y := X') =
      mapLeftAddHom (NonUnitalBimoduleHom.id R T Y₀) := rfl

end Functors

/-! ## Equivariant universal lifts -/

section Lifts

variable {S : Type uS} {R : Type uR} {T : Type uT}
  [NonUnitalRing S] [NonUnitalRing R] [NonUnitalRing T]

section LeftLift

variable {X : Type uX} [AddCommGroup X] [NonUnitalModule S X] [NonUnitalModule Rᵐᵒᵖ X]
  (hX : ActionsCommute S R X) {Y : Type uY} [AddCommGroup Y] [NonUnitalModule R Y]
  {Z : Type uZ} [AddCommGroup Z] [NonUnitalModule S Z]

theorem lift_comp_leftScalar (b : X →+ Y →+ Z) (hb : NonUnitalModuleTensor.IsBalanced R b)
    (hs : ∀ (s : S) (x : X) (y : Y), b (s • x) y = s • b x y) (s : S) :
    (NonUnitalModuleTensor.lift R b hb).comp (leftScalar hX Y s) =
      AddMonoidHom.comp (NonUnitalModule.toEndHom ‹NonUnitalModule S Z› s)
        (NonUnitalModuleTensor.lift R b hb) :=
  hom_ext R fun x y => hs s x y

/-- A balanced pairing that is `S`-equivariant in `X` lifts to an original `S`-linear map. -/
def leftLift (b : X →+ Y →+ Z) (hb : NonUnitalModuleTensor.IsBalanced R b)
    (hs : ∀ (s : S) (x : X) (y : Y), b (s • x) y = s • b x y) :
    @NonUnitalModuleHom S (Tensor R X Y) Z _ _ _ (leftModule hX Y) _ :=
  @NonUnitalModuleHom.mk S (Tensor R X Y) Z _ _ _ (leftModule hX Y) _
    (NonUnitalModuleTensor.lift R b hb)
    (fun s z => DFunLike.congr_fun (lift_comp_leftScalar hX b hb hs s) z)

@[simp] theorem leftLift_tmul (b : X →+ Y →+ Z) (hb : NonUnitalModuleTensor.IsBalanced R b)
    (hs : ∀ (s : S) (x : X) (y : Y), b (s • x) y = s • b x y) (x : X) (y : Y) :
    letI := leftModule hX Y
    leftLift hX b hb hs (tmul R X Y x y) = b x y := rfl

/-- The complete additive map is the published universal lift. -/
theorem leftLift_toAddMonoidHom (b : X →+ Y →+ Z) (hb : NonUnitalModuleTensor.IsBalanced R b)
    (hs : ∀ (s : S) (x : X) (y : Y), b (s • x) y = s • b x y) :
    letI := leftModule hX Y
    (leftLift hX b hb hs).toAddMonoidHom = NonUnitalModuleTensor.lift R b hb := rfl

/-- Uniqueness, as equality of complete `S`-linear maps. -/
theorem leftLift_unique (b : X →+ Y →+ Z) (hb : NonUnitalModuleTensor.IsBalanced R b)
    (hs : ∀ (s : S) (x : X) (y : Y), b (s • x) y = s • b x y)
    (F : @NonUnitalModuleHom S (Tensor R X Y) Z _ _ _ (leftModule hX Y) _)
    (hF : letI := leftModule hX Y; ∀ (x : X) (y : Y), F (tmul R X Y x y) = b x y) :
    F = leftLift hX b hb hs := by
  let _ := leftModule hX Y
  exact NonUnitalModuleHom.ext fun z =>
    DFunLike.congr_fun (NonUnitalModuleTensor.lift_unique R b hb F.toAddMonoidHom hF) z

end LeftLift

section RightLift

variable {X : Type uX} [AddCommGroup X] [NonUnitalModule Rᵐᵒᵖ X]
  {Y : Type uY} [AddCommGroup Y] [NonUnitalModule R Y] [NonUnitalModule Tᵐᵒᵖ Y]
  (hY : ActionsCommute R T Y) {Z : Type uZ} [AddCommGroup Z] [NonUnitalModule Tᵐᵒᵖ Z]

theorem lift_comp_rightScalar (b : X →+ Y →+ Z) (hb : NonUnitalModuleTensor.IsBalanced R b)
    (ht : ∀ (t : Tᵐᵒᵖ) (x : X) (y : Y), b x (t • y) = t • b x y) (t : Tᵐᵒᵖ) :
    (NonUnitalModuleTensor.lift R b hb).comp (rightScalar X hY t) =
      AddMonoidHom.comp (NonUnitalModule.toEndHom ‹NonUnitalModule Tᵐᵒᵖ Z› t)
        (NonUnitalModuleTensor.lift R b hb) :=
  hom_ext R fun x y => ht t x y

/-- A balanced pairing that is right `T`-equivariant in `Y` lifts to an original right
`T`-linear map. -/
def rightLift (b : X →+ Y →+ Z) (hb : NonUnitalModuleTensor.IsBalanced R b)
    (ht : ∀ (t : Tᵐᵒᵖ) (x : X) (y : Y), b x (t • y) = t • b x y) :
    @NonUnitalModuleHom Tᵐᵒᵖ (Tensor R X Y) Z _ _ _ (rightModule X hY) _ :=
  @NonUnitalModuleHom.mk Tᵐᵒᵖ (Tensor R X Y) Z _ _ _ (rightModule X hY) _
    (NonUnitalModuleTensor.lift R b hb)
    (fun t z => DFunLike.congr_fun (lift_comp_rightScalar hY b hb ht t) z)

@[simp] theorem rightLift_tmul (b : X →+ Y →+ Z) (hb : NonUnitalModuleTensor.IsBalanced R b)
    (ht : ∀ (t : Tᵐᵒᵖ) (x : X) (y : Y), b x (t • y) = t • b x y) (x : X) (y : Y) :
    letI := rightModule X hY
    rightLift hY b hb ht (tmul R X Y x y) = b x y := rfl

/-- The complete additive map is the published universal lift. -/
theorem rightLift_toAddMonoidHom (b : X →+ Y →+ Z) (hb : NonUnitalModuleTensor.IsBalanced R b)
    (ht : ∀ (t : Tᵐᵒᵖ) (x : X) (y : Y), b x (t • y) = t • b x y) :
    letI := rightModule X hY
    (rightLift hY b hb ht).toAddMonoidHom = NonUnitalModuleTensor.lift R b hb := rfl

/-- Uniqueness, as equality of complete right `T`-linear maps. -/
theorem rightLift_unique (b : X →+ Y →+ Z) (hb : NonUnitalModuleTensor.IsBalanced R b)
    (ht : ∀ (t : Tᵐᵒᵖ) (x : X) (y : Y), b x (t • y) = t • b x y)
    (F : @NonUnitalModuleHom Tᵐᵒᵖ (Tensor R X Y) Z _ _ _ (rightModule X hY) _)
    (hF : letI := rightModule X hY; ∀ (x : X) (y : Y), F (tmul R X Y x y) = b x y) :
    F = rightLift hY b hb ht := by
  let _ := rightModule X hY
  exact NonUnitalModuleHom.ext fun z =>
    DFunLike.congr_fun (NonUnitalModuleTensor.lift_unique R b hb F.toAddMonoidHom hF) z

end RightLift

section BimoduleLift

variable {X : NonUnitalBimoduleCat.{uS, uR, uX} S R} {Y : NonUnitalBimoduleCat.{uR, uT, uY} R T}
  {Z : NonUnitalBimoduleCat.{uS, uT, uZ} S T}

/-- With both equivariance equations and commuting target actions, the same universal lift
is an actual `S–T` intertwiner. -/
def lift (b : X →+ Y →+ Z) (hb : NonUnitalModuleTensor.IsBalanced R b)
    (hs : ∀ (s : S) (x : X) (y : Y), b (s • x) y = s • b x y)
    (ht : ∀ (t : Tᵐᵒᵖ) (x : X) (y : Y), b x (t • y) = t • b x y) :
    NonUnitalBimoduleHom S T (tensor X Y) Z :=
  ⟨NonUnitalModuleTensor.lift R b hb,
    fun s z => DFunLike.congr_fun (lift_comp_leftScalar X.actionsCommute b hb hs s) z,
    fun t z => DFunLike.congr_fun (lift_comp_rightScalar Y.actionsCommute b hb ht t) z⟩

@[simp] theorem lift_tmul (b : X →+ Y →+ Z) (hb : NonUnitalModuleTensor.IsBalanced R b)
    (hs : ∀ (s : S) (x : X) (y : Y), b (s • x) y = s • b x y)
    (ht : ∀ (t : Tᵐᵒᵖ) (x : X) (y : Y), b x (t • y) = t • b x y) (x : X) (y : Y) :
    lift b hb hs ht (tmul R X Y x y) = b x y := rfl

theorem lift_val (b : X →+ Y →+ Z) (hb : NonUnitalModuleTensor.IsBalanced R b)
    (hs : ∀ (s : S) (x : X) (y : Y), b (s • x) y = s • b x y)
    (ht : ∀ (t : Tᵐᵒᵖ) (x : X) (y : Y), b x (t • y) = t • b x y) :
    (lift b hb hs ht).val = NonUnitalModuleTensor.lift R b hb := rfl

theorem lift_toLeftHom (b : X →+ Y →+ Z) (hb : NonUnitalModuleTensor.IsBalanced R b)
    (hs : ∀ (s : S) (x : X) (y : Y), b (s • x) y = s • b x y)
    (ht : ∀ (t : Tᵐᵒᵖ) (x : X) (y : Y), b x (t • y) = t • b x y) :
    (lift b hb hs ht).toLeftHom = leftLift X.actionsCommute b hb hs := rfl

theorem lift_toRightHom (b : X →+ Y →+ Z) (hb : NonUnitalModuleTensor.IsBalanced R b)
    (hs : ∀ (s : S) (x : X) (y : Y), b (s • x) y = s • b x y)
    (ht : ∀ (t : Tᵐᵒᵖ) (x : X) (y : Y), b x (t • y) = t • b x y) :
    (lift b hb hs ht).toRightHom = rightLift Y.actionsCommute b hb ht := rfl

theorem lift_unique (b : X →+ Y →+ Z) (hb : NonUnitalModuleTensor.IsBalanced R b)
    (hs : ∀ (s : S) (x : X) (y : Y), b (s • x) y = s • b x y)
    (ht : ∀ (t : Tᵐᵒᵖ) (x : X) (y : Y), b x (t • y) = t • b x y)
    (F : NonUnitalBimoduleHom S T (tensor X Y) Z)
    (hF : ∀ (x : X) (y : Y), F (tmul R X Y x y) = b x y) : F = lift b hb hs ht :=
  bimoduleHom_ext hF

end BimoduleLift

end Lifts

end Langlands.Algebra.NonUnitalBimoduleTensor
