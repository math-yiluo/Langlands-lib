import Langlands.Algebra.NonUnitalBimoduleHomNaturality

set_option autoImplicit false
-- Interface abbreviations are types whose sort intentionally takes a maximum.
set_option linter.checkUnivs false

open CategoryTheory MulOpposite

namespace Langlands.Algebra.NonUnitalBimoduleHomActions

universe uS uR uT uY uY' uY'' uZ uZ' uZ''

/-! Complete unapplied types. The one-sided and bimodule natural maps are typed on exactly
the original Hom carriers, their inherited groups and the named residual actions. -/

private abbrev SourceMapInterface :=
  {S : Type uS} → {R : Type uR} → {Y : Type uY} → {Y' : Type uY'} →
  {Z : Type uZ} → {Z' : Type uZ'} →
  [s : NonUnitalRing S] → [r : NonUnitalRing R] →
  [y : AddCommGroup Y] → [y' : AddCommGroup Y'] → [z : AddCommGroup Z] → [z' : AddCommGroup Z'] →
  [sy : NonUnitalModule S Y] → [ry : NonUnitalModule Rᵐᵒᵖ Y] →
  [sy' : NonUnitalModule S Y'] → [ry' : NonUnitalModule Rᵐᵒᵖ Y'] →
  [sz : NonUnitalModule S Z] → [sz' : NonUnitalModule S Z'] →
  (hY : @ActionsCommute S R Y s r y sy ry) → (hY' : @ActionsCommute S R Y' s r y' sy' ry') →
  @NonUnitalBimoduleHom S R Y' Y s r y' y sy' ry' sy ry →
  @NonUnitalModuleHom S Z Z' s z z' sz sz' →
  @NonUnitalModuleHom R (@NonUnitalModuleHom S Y Z s y z sy sz)
    (@NonUnitalModuleHom S Y' Z' s y' z' sy' sz') r
    (@NonUnitalModuleHom.instAddCommGroup S Y Z s y z sy sz)
    (@NonUnitalModuleHom.instAddCommGroup S Y' Z' s y' z' sy' sz')
    (@sourceAction S R Y Z s r y z sy ry sz hY)
    (@sourceAction S R Y' Z' s r y' z' sy' ry' sz' hY')

example : SourceMapInterface.{uS, uR, uY, uY', uZ, uZ'} := @sourceMap
example : SourceMapInterface.{0, 1, 0, 1, 1, 0} := @sourceMap
example : SourceMapInterface.{1, 0, 1, 0, 0, 1} := @sourceMap

private abbrev TargetMapInterface :=
  {S : Type uS} → {T : Type uT} → {Y : Type uY} → {Y' : Type uY'} →
  {Z : Type uZ} → {Z' : Type uZ'} →
  [s : NonUnitalRing S] → [t : NonUnitalRing T] →
  [y : AddCommGroup Y] → [y' : AddCommGroup Y'] → [z : AddCommGroup Z] → [z' : AddCommGroup Z'] →
  [sy : NonUnitalModule S Y] → [sy' : NonUnitalModule S Y'] →
  [sz : NonUnitalModule S Z] → [tz : NonUnitalModule Tᵐᵒᵖ Z] →
  [sz' : NonUnitalModule S Z'] → [tz' : NonUnitalModule Tᵐᵒᵖ Z'] →
  (hZ : @ActionsCommute S T Z s t z sz tz) → (hZ' : @ActionsCommute S T Z' s t z' sz' tz') →
  @NonUnitalModuleHom S Y' Y s y' y sy' sy →
  @NonUnitalBimoduleHom S T Z Z' s t z z' sz tz sz' tz' →
  @NonUnitalModuleHom Tᵐᵒᵖ (@NonUnitalModuleHom S Y Z s y z sy sz)
    (@NonUnitalModuleHom S Y' Z' s y' z' sy' sz') _
    (@NonUnitalModuleHom.instAddCommGroup S Y Z s y z sy sz)
    (@NonUnitalModuleHom.instAddCommGroup S Y' Z' s y' z' sy' sz')
    (@targetAction S T Y Z s t y z sy sz tz hZ)
    (@targetAction S T Y' Z' s t y' z' sy' sz' tz' hZ')

example : TargetMapInterface.{uS, uT, uY, uY', uZ, uZ'} := @targetMap
example : TargetMapInterface.{0, 1, 0, 1, 1, 0} := @targetMap
example : TargetMapInterface.{1, 0, 1, 0, 0, 1} := @targetMap

private abbrev RightSourceMapInterface :=
  {R : Type uR} → {S : Type uS} → {Y : Type uY} → {Y' : Type uY'} →
  {Z : Type uZ} → {Z' : Type uZ'} →
  [r : NonUnitalRing R] → [s : NonUnitalRing S] →
  [y : AddCommGroup Y] → [y' : AddCommGroup Y'] → [z : AddCommGroup Z] → [z' : AddCommGroup Z'] →
  [ry : NonUnitalModule R Y] → [sy : NonUnitalModule Sᵐᵒᵖ Y] →
  [ry' : NonUnitalModule R Y'] → [sy' : NonUnitalModule Sᵐᵒᵖ Y'] →
  [sz : NonUnitalModule Sᵐᵒᵖ Z] → [sz' : NonUnitalModule Sᵐᵒᵖ Z'] →
  (hY : @ActionsCommute R S Y r s y ry sy) → (hY' : @ActionsCommute R S Y' r s y' ry' sy') →
  @NonUnitalBimoduleHom R S Y' Y r s y' y ry' sy' ry sy →
  @NonUnitalModuleHom Sᵐᵒᵖ Z Z' _ z z' sz sz' →
  @NonUnitalModuleHom Rᵐᵒᵖ (@NonUnitalModuleHom Sᵐᵒᵖ Y Z _ y z sy sz)
    (@NonUnitalModuleHom Sᵐᵒᵖ Y' Z' _ y' z' sy' sz') _
    (@NonUnitalModuleHom.instAddCommGroup Sᵐᵒᵖ Y Z _ y z sy sz)
    (@NonUnitalModuleHom.instAddCommGroup Sᵐᵒᵖ Y' Z' _ y' z' sy' sz')
    (@rightSourceAction R S Y Z r s y z ry sy sz hY)
    (@rightSourceAction R S Y' Z' r s y' z' ry' sy' sz' hY')

example : RightSourceMapInterface.{uR, uS, uY, uY', uZ, uZ'} := @rightSourceMap
example : RightSourceMapInterface.{0, 1, 0, 1, 1, 0} := @rightSourceMap
example : RightSourceMapInterface.{1, 0, 1, 0, 0, 1} := @rightSourceMap

private abbrev HomMapInterface :=
  {S : Type uS} → {R : Type uR} → {T : Type uT} → {Y : Type uY} → {Y' : Type uY'} →
  {Z : Type uZ} → {Z' : Type uZ'} →
  [s : NonUnitalRing S] → [r : NonUnitalRing R] → [t : NonUnitalRing T] →
  [y : AddCommGroup Y] → [y' : AddCommGroup Y'] → [z : AddCommGroup Z] → [z' : AddCommGroup Z'] →
  [sy : NonUnitalModule S Y] → [ry : NonUnitalModule Rᵐᵒᵖ Y] →
  [sy' : NonUnitalModule S Y'] → [ry' : NonUnitalModule Rᵐᵒᵖ Y'] →
  [sz : NonUnitalModule S Z] → [tz : NonUnitalModule Tᵐᵒᵖ Z] →
  [sz' : NonUnitalModule S Z'] → [tz' : NonUnitalModule Tᵐᵒᵖ Z'] →
  (hY : @ActionsCommute S R Y s r y sy ry) → (hY' : @ActionsCommute S R Y' s r y' sy' ry') →
  (hZ : @ActionsCommute S T Z s t z sz tz) → (hZ' : @ActionsCommute S T Z' s t z' sz' tz') →
  @NonUnitalBimoduleHom S R Y' Y s r y' y sy' ry' sy ry →
  @NonUnitalBimoduleHom S T Z Z' s t z z' sz tz sz' tz' →
  @NonUnitalBimoduleHom R T (@NonUnitalModuleHom S Y Z s y z sy sz)
    (@NonUnitalModuleHom S Y' Z' s y' z' sy' sz') r t
    (@NonUnitalModuleHom.instAddCommGroup S Y Z s y z sy sz)
    (@NonUnitalModuleHom.instAddCommGroup S Y' Z' s y' z' sy' sz')
    (@sourceAction S R Y Z s r y z sy ry sz hY) (@targetAction S T Y Z s t y z sy sz tz hZ)
    (@sourceAction S R Y' Z' s r y' z' sy' ry' sz' hY')
    (@targetAction S T Y' Z' s t y' z' sy' sz' tz' hZ')

example : HomMapInterface.{uS, uR, uT, uY, uY', uZ, uZ'} := @homMap
example : HomMapInterface.{0, 1, 0, 1, 0, 0, 1} := @homMap
example : HomMapInterface.{1, 0, 1, 0, 1, 1, 0} := @homMap

/-- The entire underlying additive map of `H(f,g)`, with all structures explicit. -/
private abbrev HomMapValInterface :=
  {S : Type uS} → {R : Type uR} → {T : Type uT} → {Y : Type uY} → {Y' : Type uY'} →
  {Z : Type uZ} → {Z' : Type uZ'} →
  [s : NonUnitalRing S] → [r : NonUnitalRing R] → [t : NonUnitalRing T] →
  [y : AddCommGroup Y] → [y' : AddCommGroup Y'] → [z : AddCommGroup Z] → [z' : AddCommGroup Z'] →
  [sy : NonUnitalModule S Y] → [ry : NonUnitalModule Rᵐᵒᵖ Y] →
  [sy' : NonUnitalModule S Y'] → [ry' : NonUnitalModule Rᵐᵒᵖ Y'] →
  [sz : NonUnitalModule S Z] → [tz : NonUnitalModule Tᵐᵒᵖ Z] →
  [sz' : NonUnitalModule S Z'] → [tz' : NonUnitalModule Tᵐᵒᵖ Z'] →
  (hY : @ActionsCommute S R Y s r y sy ry) → (hY' : @ActionsCommute S R Y' s r y' sy' ry') →
  (hZ : @ActionsCommute S T Z s t z sz tz) → (hZ' : @ActionsCommute S T Z' s t z' sz' tz') →
  (f : @NonUnitalBimoduleHom S R Y' Y s r y' y sy' ry' sy ry) →
  (g : @NonUnitalBimoduleHom S T Z Z' s t z z' sz tz sz' tz') →
  (@homMap S R T Y Y' Z Z' s r t y y' z z' sy ry sy' ry' sz tz sz' tz' hY hY' hZ hZ' f g).val =
    @mapAddHom S s Y Z Y' Z' y z y' z' sy sz sy' sz' f.toLeftHom g.toLeftHom

example : HomMapValInterface.{uS, uR, uT, uY, uY', uZ, uZ'} := @homMap_val
example : HomMapValInterface.{0, 1, 0, 1, 0, 0, 1} := @homMap_val
example : HomMapValInterface.{1, 0, 1, 0, 1, 1, 0} := @homMap_val

private abbrev HomCovariantFunctorInterface :=
  {S : Type uS} → {R : Type uR} → (T : Type uT) → {Y : Type uY} →
  [s : NonUnitalRing S] → [r : NonUnitalRing R] → [NonUnitalRing T] →
  [y : AddCommGroup Y] → [sy : NonUnitalModule S Y] → [ry : NonUnitalModule Rᵐᵒᵖ Y] →
  (hY : @ActionsCommute S R Y s r y sy ry) →
  NonUnitalBimoduleCat.{uS, uT, uZ} S T ⥤ NonUnitalBimoduleCat.{uR, uT, max uY uZ} R T

example : HomCovariantFunctorInterface.{uS, uR, uT, uY, uZ} := @homCovariantFunctor
example : HomCovariantFunctorInterface.{0, 1, 0, 1, 0} := @homCovariantFunctor
example : HomCovariantFunctorInterface.{1, 0, 1, 0, 1} := @homCovariantFunctor

private abbrev HomCovariantAdditiveInterface :=
  {S : Type uS} → {R : Type uR} → (T : Type uT) → {Y : Type uY} →
  [s : NonUnitalRing S] → [r : NonUnitalRing R] → [NonUnitalRing T] →
  [y : AddCommGroup Y] → [sy : NonUnitalModule S Y] → [ry : NonUnitalModule Rᵐᵒᵖ Y] →
  (hY : @ActionsCommute S R Y s r y sy ry) →
  (homCovariantFunctor T hY : NonUnitalBimoduleCat.{uS, uT, uZ} S T ⥤
    NonUnitalBimoduleCat.{uR, uT, max uY uZ} R T).Additive

example : HomCovariantAdditiveInterface.{uS, uR, uT, uY, uZ} := @homCovariantFunctor_additive
example : HomCovariantAdditiveInterface.{0, 1, 0, 1, 0} := @homCovariantFunctor_additive
example : HomCovariantAdditiveInterface.{1, 0, 1, 0, 1} := @homCovariantFunctor_additive

private abbrev HomContravariantFunctorInterface :=
  {S : Type uS} → (R : Type uR) → {T : Type uT} → {Z : Type uZ} →
  [s : NonUnitalRing S] → [NonUnitalRing R] → [t : NonUnitalRing T] →
  [z : AddCommGroup Z] → [sz : NonUnitalModule S Z] → [tz : NonUnitalModule Tᵐᵒᵖ Z] →
  (hZ : @ActionsCommute S T Z s t z sz tz) →
  (NonUnitalBimoduleCat.{uS, uR, uY} S R)ᵒᵖ ⥤ NonUnitalBimoduleCat.{uR, uT, max uY uZ} R T

example : HomContravariantFunctorInterface.{uS, uR, uT, uY, uZ} := @homContravariantFunctor
example : HomContravariantFunctorInterface.{0, 1, 0, 1, 0} := @homContravariantFunctor
example : HomContravariantFunctorInterface.{1, 0, 1, 0, 1} := @homContravariantFunctor

private abbrev HomContravariantAdditiveInterface :=
  {S : Type uS} → (R : Type uR) → {T : Type uT} → {Z : Type uZ} →
  [s : NonUnitalRing S] → [NonUnitalRing R] → [t : NonUnitalRing T] →
  [z : AddCommGroup Z] → [sz : NonUnitalModule S Z] → [tz : NonUnitalModule Tᵐᵒᵖ Z] →
  (hZ : @ActionsCommute S T Z s t z sz tz) →
  (homContravariantFunctor R hZ : (NonUnitalBimoduleCat.{uS, uR, uY} S R)ᵒᵖ ⥤
    NonUnitalBimoduleCat.{uR, uT, max uY uZ} R T).Additive

example : HomContravariantAdditiveInterface.{uS, uR, uT, uY, uZ} :=
  @homContravariantFunctor_additive
example : HomContravariantAdditiveInterface.{0, 1, 0, 1, 0} := @homContravariantFunctor_additive
example : HomContravariantAdditiveInterface.{1, 0, 1, 0, 1} := @homContravariantFunctor_additive

/-! Composition laws through three carriers in three distinct universes. -/

section ThreeUniverses

variable {S : Type} {R : Type 1} {T : Type 2}
  {Y : Type} {Y' : Type 1} {Y'' : Type 2} {Z : Type 2} {Z' : Type 1} {Z'' : Type}
  [NonUnitalRing S] [NonUnitalRing R] [NonUnitalRing T]
  [AddCommGroup Y] [AddCommGroup Y'] [AddCommGroup Y''] [AddCommGroup Z] [AddCommGroup Z']
  [AddCommGroup Z'']
  [NonUnitalModule S Y] [NonUnitalModule Rᵐᵒᵖ Y] [NonUnitalModule S Y']
  [NonUnitalModule Rᵐᵒᵖ Y'] [NonUnitalModule S Y''] [NonUnitalModule Rᵐᵒᵖ Y'']
  [NonUnitalModule S Z] [NonUnitalModule Tᵐᵒᵖ Z] [NonUnitalModule S Z']
  [NonUnitalModule Tᵐᵒᵖ Z'] [NonUnitalModule S Z''] [NonUnitalModule Tᵐᵒᵖ Z'']
  (hY : ActionsCommute S R Y) (hY' : ActionsCommute S R Y') (hY'' : ActionsCommute S R Y'')
  (hZ : ActionsCommute S T Z) (hZ' : ActionsCommute S T Z') (hZ'' : ActionsCommute S T Z'')
  (f : NonUnitalBimoduleHom S R Y' Y) (f' : NonUnitalBimoduleHom S R Y'' Y')
  (g : NonUnitalBimoduleHom S T Z Z') (g' : NonUnitalBimoduleHom S T Z' Z'')

example :
    homMap hY hY'' hZ hZ'' (NonUnitalBimoduleHom.comp f f') (NonUnitalBimoduleHom.comp g' g) =
      NonUnitalBimoduleHom.comp (homMap hY' hY'' hZ' hZ'' f' g') (homMap hY hY' hZ hZ' f g) :=
  homMap_comp hY hY' hY'' hZ hZ' hZ'' f g f' g'

example :
    sourceMap hY hY'' (NonUnitalBimoduleHom.comp f f') (g'.toLeftHom.comp g.toLeftHom) =
      (sourceMap hY' hY'' f' g'.toLeftHom).comp (sourceMap hY hY' f g.toLeftHom) :=
  sourceMap_comp hY hY' hY'' f g.toLeftHom f' g'.toLeftHom

example :
    targetMap hZ hZ'' (f.toLeftHom.comp f'.toLeftHom) (NonUnitalBimoduleHom.comp g' g) =
      (targetMap hZ' hZ'' f'.toLeftHom g').comp (targetMap hZ hZ' f.toLeftHom g) :=
  targetMap_comp hZ hZ' hZ'' f.toLeftHom g f'.toLeftHom g'

example (h : NonUnitalModuleHom S Y Z) (y : Y'') :
    (show NonUnitalModuleHom S Y'' Z'' from
      homMap hY hY'' hZ hZ'' (NonUnitalBimoduleHom.comp f f') (NonUnitalBimoduleHom.comp g' g) h) y =
      g' (g (h (f (f' y)))) := rfl

end ThreeUniverses

/-! Competing ring, group and original-action instances; competing actions on the Hom. -/

section Competing

variable {S : Type uS} {R : Type uR} {T : Type uT}
  {Y : Type uY} {Y' : Type uY'} {Z : Type uZ} {Z' : Type uZ'}
  [s₁ : NonUnitalRing S] [s₂ : NonUnitalRing S]
  [r₁ : NonUnitalRing R] [r₂ : NonUnitalRing R]
  [t₁ : NonUnitalRing T] [t₂ : NonUnitalRing T]
  [y₁ : AddCommGroup Y] [y₂ : AddCommGroup Y] [y₁' : AddCommGroup Y'] [y₂' : AddCommGroup Y']
  [z₁ : AddCommGroup Z] [z₂ : AddCommGroup Z] [z₁' : AddCommGroup Z'] [z₂' : AddCommGroup Z']
  (sy : @NonUnitalModule S Y s₁ y₁)
  (ry : @NonUnitalModule Rᵐᵒᵖ Y (@MulOpposite.instNonUnitalRing R r₁) y₁)
  (sy' : @NonUnitalModule S Y' s₁ y₁')
  (ry' : @NonUnitalModule Rᵐᵒᵖ Y' (@MulOpposite.instNonUnitalRing R r₁) y₁')
  (sz : @NonUnitalModule S Z s₁ z₁)
  (tz : @NonUnitalModule Tᵐᵒᵖ Z (@MulOpposite.instNonUnitalRing T t₁) z₁)
  (sz' : @NonUnitalModule S Z' s₁ z₁')
  (tz' : @NonUnitalModule Tᵐᵒᵖ Z' (@MulOpposite.instNonUnitalRing T t₁) z₁')
  (hY : @ActionsCommute S R Y s₁ r₁ y₁ sy ry) (hY' : @ActionsCommute S R Y' s₁ r₁ y₁' sy' ry')
  (hZ : @ActionsCommute S T Z s₁ t₁ z₁ sz tz) (hZ' : @ActionsCommute S T Z' s₁ t₁ z₁' sz' tz')
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
  (f : @NonUnitalBimoduleHom S R Y' Y s₁ r₁ y₁' y₁ sy' ry' sy ry)
  (g : @NonUnitalBimoduleHom S T Z Z' s₁ t₁ z₁ z₁' sz tz sz' tz')

set_option linter.overlappingInstances false in
/-- Explicit inputs give the natural map on exactly the named Hom bimodules. -/
example :
    @NonUnitalBimoduleHom R T (@NonUnitalModuleHom S Y Z s₁ y₁ z₁ sy sz)
      (@NonUnitalModuleHom S Y' Z' s₁ y₁' z₁' sy' sz') r₁ t₁
      (@NonUnitalModuleHom.instAddCommGroup S Y Z s₁ y₁ z₁ sy sz)
      (@NonUnitalModuleHom.instAddCommGroup S Y' Z' s₁ y₁' z₁' sy' sz')
      (@sourceAction S R Y Z s₁ r₁ y₁ z₁ sy ry sz hY)
      (@targetAction S T Y Z s₁ t₁ y₁ z₁ sy sz tz hZ)
      (@sourceAction S R Y' Z' s₁ r₁ y₁' z₁' sy' ry' sz' hY')
      (@targetAction S T Y' Z' s₁ t₁ y₁' z₁' sy' sz' tz' hZ') :=
  @homMap S R T Y Y' Z Z' s₁ r₁ t₁ y₁ y₁' z₁ z₁' sy ry sy' ry' sz tz sz' tz' hY hY' hZ hZ' f g

set_option linter.overlappingInstances false in
/-- The bundled one-sided Hom objects keep the named actions, not the competing ones. -/
example :
    @NonUnitalModuleCat.isModule R r₁ (@sourceHom S R Y s₁ r₁ y₁ sy ry hY Z z₁ sz) =
      @sourceAction S R Y Z s₁ r₁ y₁ z₁ sy ry sz hY ∧
    @NonUnitalModuleCat.isModule Tᵐᵒᵖ (@MulOpposite.instNonUnitalRing T t₁)
        (@targetHom S T Z s₁ t₁ z₁ sz tz Y y₁ sy hZ) =
      @targetAction S T Y Z s₁ t₁ y₁ z₁ sy sz tz hZ :=
  ⟨rfl, rfl⟩

set_option linter.overlappingInstances false in
/-- The functor objects are the named Hom bimodules. -/
example :
    (@homCovariantFunctor S R T Y s₁ r₁ t₁ y₁ sy ry hY).obj
        (@NonUnitalBimoduleCat.of S T s₁ t₁ Z z₁ sz tz hZ) =
      @hom S R T Y Z s₁ r₁ t₁ y₁ z₁ sy ry sz tz hY hZ ∧
    (@homContravariantFunctor S R T Z s₁ r₁ t₁ z₁ sz tz hZ).obj
        (Opposite.op (@NonUnitalBimoduleCat.of S R s₁ r₁ Y y₁ sy ry hY)) =
      @hom S R T Y Z s₁ r₁ t₁ y₁ z₁ sy ry sz tz hY hZ :=
  ⟨rfl, rfl⟩

end Competing

/-! With unique rings and groups, linearity is for the named scalar endomorphisms even when
competing actions on the Hom carriers are instances. -/

section CompetingHomActions

variable {S : Type uS} {R : Type uR} {T : Type uT}
  {Y : Type uY} {Y' : Type uY'} {Z : Type uZ} {Z' : Type uZ'}
  [NonUnitalRing S] [NonUnitalRing R] [NonUnitalRing T]
  [AddCommGroup Y] [AddCommGroup Y'] [AddCommGroup Z] [AddCommGroup Z']
  [NonUnitalModule S Y] [NonUnitalModule Rᵐᵒᵖ Y] [NonUnitalModule S Y']
  [NonUnitalModule Rᵐᵒᵖ Y'] [NonUnitalModule S Z] [NonUnitalModule Tᵐᵒᵖ Z]
  [NonUnitalModule S Z'] [NonUnitalModule Tᵐᵒᵖ Z']
  (hY : ActionsCommute S R Y) (hY' : ActionsCommute S R Y')
  (hZ : ActionsCommute S T Z) (hZ' : ActionsCommute S T Z')
  [NonUnitalModule R (NonUnitalModuleHom S Y Z)] [NonUnitalModule R (NonUnitalModuleHom S Y' Z')]
  [NonUnitalModule Tᵐᵒᵖ (NonUnitalModuleHom S Y Z)]
  [NonUnitalModule Tᵐᵒᵖ (NonUnitalModuleHom S Y' Z')]
  (f : NonUnitalBimoduleHom S R Y' Y) (g : NonUnitalBimoduleHom S T Z Z')

example (a : R) (h : NonUnitalModuleHom S Y Z) :
    homMap hY hY' hZ hZ' f g (NonUnitalModule.toEndHom (sourceAction hY) a h) =
      NonUnitalModule.toEndHom (sourceAction hY') a (homMap hY hY' hZ hZ' f g h) :=
  (homMap hY hY' hZ hZ' f g).map_smul_left a h

example (b : Tᵐᵒᵖ) (h : NonUnitalModuleHom S Y Z) :
    homMap hY hY' hZ hZ' f g (NonUnitalModule.toEndHom (targetAction hZ) b h) =
      NonUnitalModule.toEndHom (targetAction hZ') b (homMap hY hY' hZ hZ' f g h) :=
  (homMap hY hY' hZ hZ' f g).map_smul_right b h

example (a : R) (h : NonUnitalModuleHom S Y Z) :
    sourceMap hY hY' f g.toLeftHom (NonUnitalModule.toEndHom (sourceAction hY) a h) =
      NonUnitalModule.toEndHom (sourceAction hY') a (sourceMap hY hY' f g.toLeftHom h) :=
  (sourceMap hY hY' f g.toLeftHom).map_smul a h

example (b : Tᵐᵒᵖ) (h : NonUnitalModuleHom S Y Z) :
    targetMap hZ hZ' f.toLeftHom g (NonUnitalModule.toEndHom (targetAction hZ) b h) =
      NonUnitalModule.toEndHom (targetAction hZ') b (targetMap hZ hZ' f.toLeftHom g h) :=
  (targetMap hZ hZ' f.toLeftHom g).map_smul b h

example : (sourceHom hY Z).isModule = sourceAction hY ∧ (targetHom Y hZ).isModule = targetAction hZ :=
  ⟨rfl, rfl⟩

end CompetingHomActions

/-! Subsingleton carriers. -/

section Subsingleton

variable {S : Type uS} {R : Type uR} {T : Type uT}
  {Y : Type uY} {Y' : Type uY'} {Z : Type uZ} {Z' : Type uZ'}
  [NonUnitalRing S] [NonUnitalRing R] [NonUnitalRing T]
  [AddCommGroup Y] [AddCommGroup Y'] [AddCommGroup Z] [AddCommGroup Z']
  [NonUnitalModule S Y] [NonUnitalModule Rᵐᵒᵖ Y] [NonUnitalModule S Y']
  [NonUnitalModule Rᵐᵒᵖ Y'] [NonUnitalModule S Z] [NonUnitalModule Tᵐᵒᵖ Z]
  [NonUnitalModule S Z'] [NonUnitalModule Tᵐᵒᵖ Z']
  (hY : ActionsCommute S R Y) (hY' : ActionsCommute S R Y')
  (hZ : ActionsCommute S T Z) (hZ' : ActionsCommute S T Z')
  (f : NonUnitalBimoduleHom S R Y' Y) (g : NonUnitalBimoduleHom S T Z Z')

/-- A subsingleton new target makes every natural map zero. -/
example [Subsingleton Z'] : homMap hY hY' hZ hZ' f g = 0 :=
  NonUnitalBimoduleHom.ext fun _ => (hom_subsingleton (S := S) (Y := Y') (Z := Z')).elim _ _

/-- A subsingleton new source makes every natural map zero. -/
example [Subsingleton Y'] : homMap hY hY' hZ hZ' f g = 0 :=
  NonUnitalBimoduleHom.ext fun _ =>
    (hom_subsingleton_of_source (S := S) (Y := Y') (Z := Z')).elim _ _

example (Zc : NonUnitalBimoduleCat.{uS, uT, uZ} S T) [Subsingleton Zc] :
    Subsingleton ((homCovariantFunctor T hY).obj Zc) :=
  hom_subsingleton (S := S) (Y := Y) (Z := Zc)

example (Yc : (NonUnitalBimoduleCat.{uS, uR, uY} S R)ᵒᵖ) [Subsingleton Yc.unop] :
    Subsingleton ((homContravariantFunctor R hZ).obj Yc) :=
  hom_subsingleton_of_source (S := S) (Y := Yc.unop) (Z := Z)

end Subsingleton

/-! Nonzero integer Hom with zero original residual actions. -/

section IntegerZero

variable (S : Type uS) (R : Type uR) (T : Type uT)
  [NonUnitalRing S] [Ring R] [Ring T]

local instance naturalityIntSource : NonUnitalModule S ℤ := NonUnitalModule.zero
local instance naturalityIntSourceRight : NonUnitalModule Rᵐᵒᵖ ℤ := NonUnitalModule.zero
local instance naturalityIntTargetRight : NonUnitalModule Tᵐᵒᵖ ℤ := NonUnitalModule.zero

/-- On the nonzero Hom between zero-action copies of `ℤ`, `H(id,id)` is the nonzero identity,
while `H` is not jointly additive: doubling both maps multiplies by four. -/
example :
    let hY := actionsCommute_zero_left (A := S) (B := R) (M := ℤ)
    let hZ := actionsCommute_zero_left (A := S) (B := T) (M := ℤ)
    let f := NonUnitalBimoduleHom.id S R ℤ
    let g := NonUnitalBimoduleHom.id S T ℤ
    homMap hY hY hZ hZ f g = NonUnitalBimoduleHom.id R T (hom hY hZ) ∧
      homMap hY hY hZ hZ f g ≠ 0 ∧
      homMap hY hY hZ hZ (f + f) (g + g) ≠ homMap hY hY hZ hZ f g + homMap hY hY hZ hZ f g := by
  intro hY hZ f g
  refine ⟨rfl, fun e => ?_, fun e => ?_⟩
  · have bad := congrArg (fun φ : NonUnitalBimoduleHom R T (hom hY hZ) (hom hY hZ) =>
      (show NonUnitalModuleHom S ℤ ℤ from φ (NonUnitalModuleHom.id S ℤ)) 1) e
    change (1 : ℤ) = 0 at bad
    exact one_ne_zero bad
  · have bad := congrArg (fun φ : NonUnitalBimoduleHom R T (hom hY hZ) (hom hY hZ) =>
      (show NonUnitalModuleHom S ℤ ℤ from φ (NonUnitalModuleHom.id S ℤ)) 1) e
    change ((1 : ℤ) + 1) + (1 + 1) = 1 + 1 at bad
    norm_num at bad

/-- The covariant functor sends the identity of the zero-action `ℤ` to a nonzero map whose
target has zero residual actions. -/
example :
    let hY := actionsCommute_zero_left (A := S) (B := R) (M := ℤ)
    let Zc := NonUnitalBimoduleCat.of S T ℤ (actionsCommute_zero_left (A := S) (B := T) (M := ℤ))
    (homCovariantFunctor T hY).map (𝟙 Zc) ≠ 0 ∧
      (∀ r : R, NonUnitalModule.toEndHom ((homCovariantFunctor T hY).obj Zc).isLeftModule r = 0) ∧
      ∀ t : Tᵐᵒᵖ,
        NonUnitalModule.toEndHom ((homCovariantFunctor T hY).obj Zc).isRightModule t = 0 := by
  intro hY Zc
  refine ⟨fun e => ?_, fun r => ?_, fun t => ?_⟩
  · have bad := congrArg (fun φ : NonUnitalBimoduleHom R T (hom hY Zc.actionsCommute)
        (hom hY Zc.actionsCommute) =>
      (show NonUnitalModuleHom S ℤ ℤ from φ (NonUnitalModuleHom.id S ℤ)) 1) e
    change (1 : ℤ) = 0 at bad
    exact one_ne_zero bad
  · exact sourceAction_toEndHom_eq_zero _ (fun _ _ => rfl) r
  · exact targetAction_toEndHom_eq_zero _ (fun _ _ => rfl) t

end IntegerZero

end Langlands.Algebra.NonUnitalBimoduleHomActions
