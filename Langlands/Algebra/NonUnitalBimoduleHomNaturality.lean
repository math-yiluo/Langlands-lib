import Langlands.Algebra.NonUnitalBimoduleHomActions
import Mathlib.CategoryTheory.Preadditive.Opposite

/-!
# Natural maps and fixed-variable functors on residual-action Hom spaces

Internal arbitrary-ring prerequisites for Renard (9 July 2026), I.2.2–I.2.3. The
named residual actions `sourceAction`, `targetAction` and `rightSourceAction` on the
published original Hom `NonUnitalModuleHom S Y Z` are bundled as one-sided module
objects, and the maps `h ↦ g ∘ h ∘ f` are shown to be linear for them. For
bimodule intertwiners this gives the actual `R`–`T` bimodule intertwiner between the
Hom bimodules `hom`, with identity, composition and separate additivity laws, and
the two fixed-variable additive functors.
-/

set_option autoImplicit false

open CategoryTheory MulOpposite

namespace Langlands.Algebra.NonUnitalBimoduleHomActions

universe uS uR uT uY uY' uY'' uZ uZ' uZ''

/-! ### Identity, composition and separate additivity of `h ↦ g ∘ h ∘ f` -/

section Composition

variable {S : Type uS} [NonUnitalRing S]
  {Y : Type uY} {Y' : Type uY'} {Y'' : Type uY''} {Z : Type uZ} {Z' : Type uZ'}
  {Z'' : Type uZ''}
  [AddCommGroup Y] [AddCommGroup Y'] [AddCommGroup Y''] [AddCommGroup Z] [AddCommGroup Z']
  [AddCommGroup Z'']
  [NonUnitalModule S Y] [NonUnitalModule S Y'] [NonUnitalModule S Y'']
  [NonUnitalModule S Z] [NonUnitalModule S Z'] [NonUnitalModule S Z'']

theorem precomposeAddHom_id :
    precomposeAddHom (Z := Z) (NonUnitalModuleHom.id S Y) = AddMonoidHom.id _ := rfl

theorem postcomposeAddHom_id :
    postcomposeAddHom (Y := Y) (NonUnitalModuleHom.id S Z) = AddMonoidHom.id _ := rfl

/-- Precomposition is contravariant in the source map. -/
theorem precomposeAddHom_comp (f : NonUnitalModuleHom S Y' Y)
    (f' : NonUnitalModuleHom S Y'' Y') :
    precomposeAddHom (Z := Z) (f.comp f') = (precomposeAddHom f').comp (precomposeAddHom f) :=
  rfl

/-- Postcomposition is covariant in the target map. -/
theorem postcomposeAddHom_comp (g : NonUnitalModuleHom S Z Z')
    (g' : NonUnitalModuleHom S Z' Z'') :
    postcomposeAddHom (Y := Y) (g'.comp g) = (postcomposeAddHom g').comp (postcomposeAddHom g) :=
  rfl

/-- Precomposition and postcomposition commute. -/
theorem mapAddHom_eq_precomposeAddHom_comp (f : NonUnitalModuleHom S Y' Y)
    (g : NonUnitalModuleHom S Z Z') :
    mapAddHom f g = (precomposeAddHom f).comp (postcomposeAddHom g) := rfl

theorem mapAddHom_id :
    mapAddHom (NonUnitalModuleHom.id S Y) (NonUnitalModuleHom.id S Z) = AddMonoidHom.id _ :=
  rfl

/-- Whole-map composition law `H(f ∘ f', g' ∘ g) = H(f', g') ∘ H(f, g)`. -/
theorem mapAddHom_comp (f : NonUnitalModuleHom S Y' Y) (f' : NonUnitalModuleHom S Y'' Y')
    (g : NonUnitalModuleHom S Z Z') (g' : NonUnitalModuleHom S Z' Z'') :
    mapAddHom (f.comp f') (g'.comp g) = (mapAddHom f' g').comp (mapAddHom f g) := rfl

/-- Additivity in the source map, for a fixed target map. -/
theorem mapAddHom_add_left (f f' : NonUnitalModuleHom S Y' Y) (g : NonUnitalModuleHom S Z Z') :
    mapAddHom (f + f') g = mapAddHom f g + mapAddHom f' g := by
  refine AddMonoidHom.ext fun h => NonUnitalModuleHom.ext fun y => ?_
  change g (h (f y + f' y)) = g (h (f y)) + g (h (f' y))
  rw [NonUnitalModuleHom.map_add, NonUnitalModuleHom.map_add]

theorem mapAddHom_zero_left (g : NonUnitalModuleHom S Z Z') :
    mapAddHom (0 : NonUnitalModuleHom S Y' Y) g = 0 := by
  refine AddMonoidHom.ext fun h => NonUnitalModuleHom.ext fun y => ?_
  change g (h 0) = 0
  rw [NonUnitalModuleHom.map_zero, NonUnitalModuleHom.map_zero]

/-- Additivity in the target map, for a fixed source map. -/
theorem mapAddHom_add_right (f : NonUnitalModuleHom S Y' Y) (g g' : NonUnitalModuleHom S Z Z') :
    mapAddHom f (g + g') = mapAddHom f g + mapAddHom f g' := by
  refine AddMonoidHom.ext fun h => NonUnitalModuleHom.ext fun y => ?_
  rfl

theorem mapAddHom_zero_right (f : NonUnitalModuleHom S Y' Y) :
    mapAddHom f (0 : NonUnitalModuleHom S Z Z') = 0 := by
  refine AddMonoidHom.ext fun h => NonUnitalModuleHom.ext fun y => ?_
  rfl

end Composition

/-! ### Bundled one-sided Hom modules -/

section SourceObject

variable {S : Type uS} {R : Type uR} {Y : Type uY}
  [NonUnitalRing S] [NonUnitalRing R] [AddCommGroup Y]
  [NonUnitalModule S Y] [NonUnitalModule Rᵐᵒᵖ Y]

/-- The original Hom with only its source-precomposition left `R`-action; `Z` needs only
its left `S`-action. -/
def sourceHom (hY : ActionsCommute S R Y) (Z : Type uZ) [AddCommGroup Z]
    [NonUnitalModule S Z] : NonUnitalModuleCat.{uR, max uY uZ} R :=
  @NonUnitalModuleCat.mk R _ (NonUnitalModuleHom S Y Z) _ (sourceAction hY)

variable (hY : ActionsCommute S R Y) (Z : Type uZ) [AddCommGroup Z] [NonUnitalModule S Z]

theorem sourceHom_carrier : (sourceHom hY Z).carrier = NonUnitalModuleHom S Y Z := rfl

theorem sourceHom_isAddCommGroup : (sourceHom hY Z).isAddCommGroup =
    NonUnitalModuleHom.instAddCommGroup (A := S) (M := Y) (N := Z) := rfl

theorem sourceHom_isModule : (sourceHom hY Z).isModule = sourceAction hY := rfl

end SourceObject

section TargetObject

variable {S : Type uS} {T : Type uT} {Z : Type uZ}
  [NonUnitalRing S] [NonUnitalRing T] [AddCommGroup Z]
  [NonUnitalModule S Z] [NonUnitalModule Tᵐᵒᵖ Z]

/-- The original Hom with only its target-postcomposition right `T`-action; `Y` needs only
its left `S`-action. -/
def targetHom (Y : Type uY) [AddCommGroup Y] [NonUnitalModule S Y]
    (hZ : ActionsCommute S T Z) : NonUnitalModuleCat.{uT, max uY uZ} Tᵐᵒᵖ :=
  @NonUnitalModuleCat.mk Tᵐᵒᵖ _ (NonUnitalModuleHom S Y Z) _ (targetAction hZ)

variable (Y : Type uY) [AddCommGroup Y] [NonUnitalModule S Y] (hZ : ActionsCommute S T Z)

theorem targetHom_carrier : (targetHom Y hZ).carrier = NonUnitalModuleHom S Y Z := rfl

theorem targetHom_isAddCommGroup : (targetHom Y hZ).isAddCommGroup =
    NonUnitalModuleHom.instAddCommGroup (A := S) (M := Y) (N := Z) := rfl

theorem targetHom_isModule : (targetHom Y hZ).isModule = targetAction hZ := rfl

end TargetObject

section RightSourceObject

variable {R : Type uR} {S : Type uS} {Y : Type uY}
  [NonUnitalRing R] [NonUnitalRing S] [AddCommGroup Y]
  [NonUnitalModule R Y] [NonUnitalModule Sᵐᵒᵖ Y]

/-- The original right `S`-linear Hom with only its source-precomposition right
`R`-action; `Z` needs only its right `S`-action. -/
def rightSourceHom (hY : ActionsCommute R S Y) (Z : Type uZ) [AddCommGroup Z]
    [NonUnitalModule Sᵐᵒᵖ Z] : NonUnitalModuleCat.{uR, max uY uZ} Rᵐᵒᵖ :=
  @NonUnitalModuleCat.mk Rᵐᵒᵖ _ (NonUnitalModuleHom Sᵐᵒᵖ Y Z) _ (rightSourceAction hY)

variable (hY : ActionsCommute R S Y) (Z : Type uZ) [AddCommGroup Z] [NonUnitalModule Sᵐᵒᵖ Z]

theorem rightSourceHom_carrier :
    (rightSourceHom hY Z).carrier = NonUnitalModuleHom Sᵐᵒᵖ Y Z := rfl

theorem rightSourceHom_isAddCommGroup : (rightSourceHom hY Z).isAddCommGroup =
    NonUnitalModuleHom.instAddCommGroup (A := Sᵐᵒᵖ) (M := Y) (N := Z) := rfl

theorem rightSourceHom_isModule : (rightSourceHom hY Z).isModule = rightSourceAction hY := rfl

end RightSourceObject

section ForgetHom

variable {S : Type uS} {R : Type uR} {T : Type uT} {Y : Type uY} {Z : Type uZ}
  [NonUnitalRing S] [NonUnitalRing R] [NonUnitalRing T]
  [AddCommGroup Y] [AddCommGroup Z]
  [NonUnitalModule S Y] [NonUnitalModule Rᵐᵒᵖ Y]
  [NonUnitalModule S Z] [NonUnitalModule Tᵐᵒᵖ Z]
  (hY : ActionsCommute S R Y) (hZ : ActionsCommute S T Z)

/-- Forgetting the right action of the bundled Hom bimodule gives the source object. -/
theorem forgetToLeft_obj_hom :
    (NonUnitalBimoduleCat.forgetToLeft R T).obj (hom hY hZ) = sourceHom hY Z := rfl

/-- Forgetting the left action of the bundled Hom bimodule gives the target object. -/
theorem forgetToRight_obj_hom :
    (NonUnitalBimoduleCat.forgetToRight R T).obj (hom hY hZ) = targetHom Y hZ := rfl

end ForgetHom

/-! ### One-sided natural maps -/

section SourceMap

variable {S : Type uS} {R : Type uR}
  {Y : Type uY} {Y' : Type uY'} {Y'' : Type uY''} {Z : Type uZ} {Z' : Type uZ'}
  {Z'' : Type uZ''}
  [NonUnitalRing S] [NonUnitalRing R]
  [AddCommGroup Y] [AddCommGroup Y'] [AddCommGroup Y''] [AddCommGroup Z] [AddCommGroup Z']
  [AddCommGroup Z'']
  [NonUnitalModule S Y] [NonUnitalModule Rᵐᵒᵖ Y] [NonUnitalModule S Y']
  [NonUnitalModule Rᵐᵒᵖ Y'] [NonUnitalModule S Y''] [NonUnitalModule Rᵐᵒᵖ Y'']
  [NonUnitalModule S Z] [NonUnitalModule S Z'] [NonUnitalModule S Z'']
  (hY : ActionsCommute S R Y) (hY' : ActionsCommute S R Y') (hY'' : ActionsCommute S R Y'')

/-- `h ↦ g ∘ h ∘ f` is left `R`-linear for the source-precomposition actions, for an
`S`–`R` bimodule intertwiner `f` and a left `S`-linear `g`. -/
def sourceMap (f : NonUnitalBimoduleHom S R Y' Y) (g : NonUnitalModuleHom S Z Z') :
    NonUnitalModuleHom R (sourceHom hY Z) (sourceHom hY' Z') where
  toAddMonoidHom := mapAddHom f.toLeftHom g
  map_smul' r (h : NonUnitalModuleHom S Y Z) := NonUnitalModuleHom.ext fun y =>
    congrArg (fun y'' => g (h y'')) (f.map_op_smul r y).symm

variable (f : NonUnitalBimoduleHom S R Y' Y) (g : NonUnitalModuleHom S Z Z')

theorem sourceMap_toAddMonoidHom :
    (sourceMap hY hY' f g).toAddMonoidHom = mapAddHom f.toLeftHom g := rfl

theorem sourceMap_apply (h : NonUnitalModuleHom S Y Z) :
    sourceMap hY hY' f g h = g.comp (h.comp f.toLeftHom) := rfl

theorem sourceMap_apply_apply (h : NonUnitalModuleHom S Y Z) (y : Y') :
    (show NonUnitalModuleHom S Y' Z' from sourceMap hY hY' f g h) y = g (h (f y)) := rfl

theorem sourceMap_id :
    sourceMap hY hY (NonUnitalBimoduleHom.id S R Y) (NonUnitalModuleHom.id S Z) =
      NonUnitalModuleHom.id R (sourceHom hY Z) := rfl

/-- Composition law `(f ∘ f', g' ∘ g) ↦ (f', g') ∘ (f, g)`. -/
theorem sourceMap_comp (f' : NonUnitalBimoduleHom S R Y'' Y') (g' : NonUnitalModuleHom S Z' Z'') :
    sourceMap hY hY'' (NonUnitalBimoduleHom.comp f f') (g'.comp g) =
      (sourceMap hY' hY'' f' g').comp (sourceMap hY hY' f g) := rfl

end SourceMap

section TargetMap

variable {S : Type uS} {T : Type uT}
  {Y : Type uY} {Y' : Type uY'} {Y'' : Type uY''} {Z : Type uZ} {Z' : Type uZ'}
  {Z'' : Type uZ''}
  [NonUnitalRing S] [NonUnitalRing T]
  [AddCommGroup Y] [AddCommGroup Y'] [AddCommGroup Y''] [AddCommGroup Z] [AddCommGroup Z']
  [AddCommGroup Z'']
  [NonUnitalModule S Y] [NonUnitalModule S Y'] [NonUnitalModule S Y'']
  [NonUnitalModule S Z] [NonUnitalModule Tᵐᵒᵖ Z] [NonUnitalModule S Z']
  [NonUnitalModule Tᵐᵒᵖ Z'] [NonUnitalModule S Z''] [NonUnitalModule Tᵐᵒᵖ Z'']
  (hZ : ActionsCommute S T Z) (hZ' : ActionsCommute S T Z') (hZ'' : ActionsCommute S T Z'')

/-- `h ↦ g ∘ h ∘ f` is right `T`-linear for the target-postcomposition actions, for a
left `S`-linear `f` and an `S`–`T` bimodule intertwiner `g`. -/
def targetMap (f : NonUnitalModuleHom S Y' Y) (g : NonUnitalBimoduleHom S T Z Z') :
    NonUnitalModuleHom Tᵐᵒᵖ (targetHom Y hZ) (targetHom Y' hZ') where
  toAddMonoidHom := mapAddHom f g.toLeftHom
  map_smul' t (h : NonUnitalModuleHom S Y Z) :=
    NonUnitalModuleHom.ext fun y => g.map_smul_right t (h (f y))

variable (f : NonUnitalModuleHom S Y' Y) (g : NonUnitalBimoduleHom S T Z Z')

theorem targetMap_toAddMonoidHom :
    (targetMap hZ hZ' f g).toAddMonoidHom = mapAddHom f g.toLeftHom := rfl

theorem targetMap_apply (h : NonUnitalModuleHom S Y Z) :
    targetMap hZ hZ' f g h = g.toLeftHom.comp (h.comp f) := rfl

theorem targetMap_apply_apply (h : NonUnitalModuleHom S Y Z) (y : Y') :
    (show NonUnitalModuleHom S Y' Z' from targetMap hZ hZ' f g h) y = g (h (f y)) := rfl

theorem targetMap_id :
    targetMap hZ hZ (NonUnitalModuleHom.id S Y) (NonUnitalBimoduleHom.id S T Z) =
      NonUnitalModuleHom.id Tᵐᵒᵖ (targetHom Y hZ) := rfl

/-- Composition law `(f ∘ f', g' ∘ g) ↦ (f', g') ∘ (f, g)`. -/
theorem targetMap_comp (f' : NonUnitalModuleHom S Y'' Y') (g' : NonUnitalBimoduleHom S T Z' Z'') :
    targetMap hZ hZ'' (f.comp f') (NonUnitalBimoduleHom.comp g' g) =
      (targetMap hZ' hZ'' f' g').comp (targetMap hZ hZ' f g) := rfl

end TargetMap

section RightSourceMap

variable {R : Type uR} {S : Type uS}
  {Y : Type uY} {Y' : Type uY'} {Y'' : Type uY''} {Z : Type uZ} {Z' : Type uZ'}
  {Z'' : Type uZ''}
  [NonUnitalRing R] [NonUnitalRing S]
  [AddCommGroup Y] [AddCommGroup Y'] [AddCommGroup Y''] [AddCommGroup Z] [AddCommGroup Z']
  [AddCommGroup Z'']
  [NonUnitalModule R Y] [NonUnitalModule Sᵐᵒᵖ Y] [NonUnitalModule R Y']
  [NonUnitalModule Sᵐᵒᵖ Y'] [NonUnitalModule R Y''] [NonUnitalModule Sᵐᵒᵖ Y'']
  [NonUnitalModule Sᵐᵒᵖ Z] [NonUnitalModule Sᵐᵒᵖ Z'] [NonUnitalModule Sᵐᵒᵖ Z'']
  (hY : ActionsCommute R S Y) (hY' : ActionsCommute R S Y') (hY'' : ActionsCommute R S Y'')

/-- `h ↦ g ∘ h ∘ f` is right `R`-linear for the right-handed source-precomposition
actions, for an `R`–`S` bimodule intertwiner `f` and a right `S`-linear `g`. -/
def rightSourceMap (f : NonUnitalBimoduleHom R S Y' Y) (g : NonUnitalModuleHom Sᵐᵒᵖ Z Z') :
    NonUnitalModuleHom Rᵐᵒᵖ (rightSourceHom hY Z) (rightSourceHom hY' Z') where
  toAddMonoidHom := mapAddHom f.toRightHom g
  map_smul' r (h : NonUnitalModuleHom Sᵐᵒᵖ Y Z) := NonUnitalModuleHom.ext fun y =>
    congrArg (fun y'' => g (h y'')) (f.map_smul_left r.unop y).symm

variable (f : NonUnitalBimoduleHom R S Y' Y) (g : NonUnitalModuleHom Sᵐᵒᵖ Z Z')

theorem rightSourceMap_toAddMonoidHom :
    (rightSourceMap hY hY' f g).toAddMonoidHom = mapAddHom f.toRightHom g := rfl

theorem rightSourceMap_apply (h : NonUnitalModuleHom Sᵐᵒᵖ Y Z) :
    rightSourceMap hY hY' f g h = g.comp (h.comp f.toRightHom) := rfl

theorem rightSourceMap_apply_apply (h : NonUnitalModuleHom Sᵐᵒᵖ Y Z) (y : Y') :
    (show NonUnitalModuleHom Sᵐᵒᵖ Y' Z' from rightSourceMap hY hY' f g h) y = g (h (f y)) :=
  rfl

theorem rightSourceMap_id :
    rightSourceMap hY hY (NonUnitalBimoduleHom.id R S Y) (NonUnitalModuleHom.id Sᵐᵒᵖ Z) =
      NonUnitalModuleHom.id Rᵐᵒᵖ (rightSourceHom hY Z) := rfl

/-- Composition law `(f ∘ f', g' ∘ g) ↦ (f', g') ∘ (f, g)`. -/
theorem rightSourceMap_comp (f' : NonUnitalBimoduleHom R S Y'' Y')
    (g' : NonUnitalModuleHom Sᵐᵒᵖ Z' Z'') :
    rightSourceMap hY hY'' (NonUnitalBimoduleHom.comp f f') (g'.comp g) =
      (rightSourceMap hY' hY'' f' g').comp (rightSourceMap hY hY' f g) := rfl

end RightSourceMap

/-! ### The bimodule natural map -/

section HomMap

variable {S : Type uS} {R : Type uR} {T : Type uT}
  {Y : Type uY} {Y' : Type uY'} {Y'' : Type uY''} {Z : Type uZ} {Z' : Type uZ'}
  {Z'' : Type uZ''}
  [NonUnitalRing S] [NonUnitalRing R] [NonUnitalRing T]
  [AddCommGroup Y] [AddCommGroup Y'] [AddCommGroup Y''] [AddCommGroup Z] [AddCommGroup Z']
  [AddCommGroup Z'']
  [NonUnitalModule S Y] [NonUnitalModule Rᵐᵒᵖ Y] [NonUnitalModule S Y']
  [NonUnitalModule Rᵐᵒᵖ Y'] [NonUnitalModule S Y''] [NonUnitalModule Rᵐᵒᵖ Y'']
  [NonUnitalModule S Z] [NonUnitalModule Tᵐᵒᵖ Z] [NonUnitalModule S Z']
  [NonUnitalModule Tᵐᵒᵖ Z'] [NonUnitalModule S Z''] [NonUnitalModule Tᵐᵒᵖ Z'']
  (hY : ActionsCommute S R Y) (hY' : ActionsCommute S R Y') (hY'' : ActionsCommute S R Y'')
  (hZ : ActionsCommute S T Z) (hZ' : ActionsCommute S T Z') (hZ'' : ActionsCommute S T Z'')

/-- The actual `R`–`T` bimodule intertwiner `H(f,g)(h) = g ∘ h ∘ f` between Hom
bimodules, for bimodule intertwiners `f : Y' → Y` and `g : Z → Z'`. -/
def homMap (f : NonUnitalBimoduleHom S R Y' Y) (g : NonUnitalBimoduleHom S T Z Z') :
    NonUnitalBimoduleHom R T (hom hY hZ) (hom hY' hZ') :=
  ⟨mapAddHom f.toLeftHom g.toLeftHom, (sourceMap hY hY' f g.toLeftHom).map_smul',
    (targetMap hZ hZ' f.toLeftHom g).map_smul'⟩

variable (f : NonUnitalBimoduleHom S R Y' Y) (g : NonUnitalBimoduleHom S T Z Z')

/-- The entire underlying additive map is `mapAddHom`. -/
theorem homMap_val : (homMap hY hY' hZ hZ' f g).val = mapAddHom f.toLeftHom g.toLeftHom := rfl

/-- The entire underlying additive map is precomposition by `f` followed by
postcomposition by `g`. -/
theorem homMap_val_eq_comp : (homMap hY hY' hZ hZ' f g).val =
    (postcomposeAddHom g.toLeftHom).comp (precomposeAddHom f.toLeftHom) := rfl

theorem homMap_apply (h : NonUnitalModuleHom S Y Z) :
    homMap hY hY' hZ hZ' f g h = g.toLeftHom.comp (h.comp f.toLeftHom) := rfl

theorem homMap_apply_apply (h : NonUnitalModuleHom S Y Z) (y : Y') :
    (show NonUnitalModuleHom S Y' Z' from homMap hY hY' hZ hZ' f g h) y = g (h (f y)) := rfl

/-- The left `R`-linear projection is the one-sided source map. -/
theorem homMap_toLeftHom :
    (homMap hY hY' hZ hZ' f g).toLeftHom = sourceMap hY hY' f g.toLeftHom := rfl

/-- The right `T`-linear projection is the one-sided target map. -/
theorem homMap_toRightHom :
    (homMap hY hY' hZ hZ' f g).toRightHom = targetMap hZ hZ' f.toLeftHom g := rfl

theorem homMap_id :
    homMap hY hY hZ hZ (NonUnitalBimoduleHom.id S R Y) (NonUnitalBimoduleHom.id S T Z) =
      NonUnitalBimoduleHom.id R T (hom hY hZ) := rfl

/-- Whole-map composition law `H(f ∘ f', g' ∘ g) = H(f', g') ∘ H(f, g)`. -/
theorem homMap_comp (f' : NonUnitalBimoduleHom S R Y'' Y')
    (g' : NonUnitalBimoduleHom S T Z' Z'') :
    homMap hY hY'' hZ hZ'' (NonUnitalBimoduleHom.comp f f') (NonUnitalBimoduleHom.comp g' g) =
      NonUnitalBimoduleHom.comp (homMap hY' hY'' hZ' hZ'' f' g') (homMap hY hY' hZ hZ' f g) :=
  rfl

/-- Additivity in the source intertwiner, for a fixed target intertwiner. -/
theorem homMap_add_left (f' : NonUnitalBimoduleHom S R Y' Y) :
    homMap hY hY' hZ hZ' (f + f') g = homMap hY hY' hZ hZ' f g + homMap hY hY' hZ hZ' f' g :=
  Subtype.ext (mapAddHom_add_left f.toLeftHom f'.toLeftHom g.toLeftHom)

theorem homMap_zero_left :
    homMap hY hY' hZ hZ' (0 : NonUnitalBimoduleHom S R Y' Y) g = 0 :=
  Subtype.ext (mapAddHom_zero_left g.toLeftHom)

/-- Additivity in the target intertwiner, for a fixed source intertwiner. -/
theorem homMap_add_right (g' : NonUnitalBimoduleHom S T Z Z') :
    homMap hY hY' hZ hZ' f (g + g') = homMap hY hY' hZ hZ' f g + homMap hY hY' hZ hZ' f g' :=
  Subtype.ext (mapAddHom_add_right f.toLeftHom g.toLeftHom g'.toLeftHom)

theorem homMap_zero_right :
    homMap hY hY' hZ hZ' f (0 : NonUnitalBimoduleHom S T Z Z') = 0 :=
  Subtype.ext (mapAddHom_zero_right f.toLeftHom)

/-- `f ↦ H(f, g)` as an additive map, for a fixed target intertwiner `g`. -/
def homMapAddHomLeft :
    NonUnitalBimoduleHom S R Y' Y →+ NonUnitalBimoduleHom R T (hom hY hZ) (hom hY' hZ') where
  toFun f := homMap hY hY' hZ hZ' f g
  map_zero' := homMap_zero_left hY hY' hZ hZ' g
  map_add' f f' := homMap_add_left hY hY' hZ hZ' f g f'

/-- `g ↦ H(f, g)` as an additive map, for a fixed source intertwiner `f`. -/
def homMapAddHomRight :
    NonUnitalBimoduleHom S T Z Z' →+ NonUnitalBimoduleHom R T (hom hY hZ) (hom hY' hZ') where
  toFun g := homMap hY hY' hZ hZ' f g
  map_zero' := homMap_zero_right hY hY' hZ hZ' f
  map_add' g g' := homMap_add_right hY hY' hZ hZ' f g g'

@[simp] theorem homMapAddHomLeft_apply :
    homMapAddHomLeft hY hY' hZ hZ' g f = homMap hY hY' hZ hZ' f g := rfl

@[simp] theorem homMapAddHomRight_apply :
    homMapAddHomRight hY hY' hZ hZ' f g = homMap hY hY' hZ hZ' f g := rfl

end HomMap

/-! ### Fixed-variable additive functors -/

section Covariant

variable {S : Type uS} {R : Type uR} (T : Type uT) {Y : Type uY}
  [NonUnitalRing S] [NonUnitalRing R] [NonUnitalRing T]
  [AddCommGroup Y] [NonUnitalModule S Y] [NonUnitalModule Rᵐᵒᵖ Y]
  (hY : ActionsCommute S R Y)

/-- For a fixed `S`–`R` bimodule `Y`, the covariant Hom functor `Z ↦ Hom_S(Y, Z)` from
`S`–`T` bimodules to `R`–`T` bimodules, landing in the carrier universe `max uY uZ`. -/
def homCovariantFunctor :
    NonUnitalBimoduleCat.{uS, uT, uZ} S T ⥤ NonUnitalBimoduleCat.{uR, uT, max uY uZ} R T where
  obj Z := hom hY Z.actionsCommute
  map {Z Z'} g :=
    homMap hY hY Z.actionsCommute Z'.actionsCommute (NonUnitalBimoduleHom.id S R Y) g
  map_id _ := rfl
  map_comp _ _ := rfl

instance homCovariantFunctor_additive :
    (homCovariantFunctor T hY : NonUnitalBimoduleCat.{uS, uT, uZ} S T ⥤
      NonUnitalBimoduleCat.{uR, uT, max uY uZ} R T).Additive where
  map_add {Z Z' g g'} :=
    homMap_add_right hY hY Z.actionsCommute Z'.actionsCommute (NonUnitalBimoduleHom.id S R Y) g g'

theorem homCovariantFunctor_obj (Z : NonUnitalBimoduleCat.{uS, uT, uZ} S T) :
    (homCovariantFunctor T hY).obj Z = hom hY Z.actionsCommute := rfl

theorem homCovariantFunctor_obj_carrier (Z : NonUnitalBimoduleCat.{uS, uT, uZ} S T) :
    ((homCovariantFunctor T hY).obj Z).carrier = NonUnitalModuleHom S Y Z := rfl

theorem homCovariantFunctor_map {Z Z' : NonUnitalBimoduleCat.{uS, uT, uZ} S T} (g : Z ⟶ Z') :
    (homCovariantFunctor T hY).map g =
      homMap hY hY Z.actionsCommute Z'.actionsCommute (NonUnitalBimoduleHom.id S R Y) g := rfl

/-- The entire underlying additive map of a covariant map is postcomposition. -/
theorem homCovariantFunctor_map_val {Z Z' : NonUnitalBimoduleCat.{uS, uT, uZ} S T}
    (g : Z ⟶ Z') :
    ((homCovariantFunctor T hY).map g).val =
      postcomposeAddHom (Y := Y) (NonUnitalBimoduleHom.toLeftHom g) := rfl

end Covariant

section Contravariant

variable {S : Type uS} (R : Type uR) {T : Type uT} {Z : Type uZ}
  [NonUnitalRing S] [NonUnitalRing R] [NonUnitalRing T]
  [AddCommGroup Z] [NonUnitalModule S Z] [NonUnitalModule Tᵐᵒᵖ Z]
  (hZ : ActionsCommute S T Z)

/-- For a fixed `S`–`T` bimodule `Z`, the contravariant Hom functor `Y ↦ Hom_S(Y, Z)` from
the opposite of `S`–`R` bimodules to `R`–`T` bimodules, landing in the carrier universe
`max uY uZ`. -/
def homContravariantFunctor :
    (NonUnitalBimoduleCat.{uS, uR, uY} S R)ᵒᵖ ⥤ NonUnitalBimoduleCat.{uR, uT, max uY uZ} R T where
  obj Y := hom Y.unop.actionsCommute hZ
  map {Y Y'} f :=
    homMap Y.unop.actionsCommute Y'.unop.actionsCommute hZ hZ f.unop
      (NonUnitalBimoduleHom.id S T Z)
  map_id _ := rfl
  map_comp _ _ := rfl

instance homContravariantFunctor_additive :
    (homContravariantFunctor R hZ : (NonUnitalBimoduleCat.{uS, uR, uY} S R)ᵒᵖ ⥤
      NonUnitalBimoduleCat.{uR, uT, max uY uZ} R T).Additive where
  map_add {Y Y' f f'} :=
    homMap_add_left Y.unop.actionsCommute Y'.unop.actionsCommute hZ hZ f.unop
      (NonUnitalBimoduleHom.id S T Z) f'.unop

theorem homContravariantFunctor_obj (Y : (NonUnitalBimoduleCat.{uS, uR, uY} S R)ᵒᵖ) :
    (homContravariantFunctor R hZ).obj Y = hom Y.unop.actionsCommute hZ := rfl

theorem homContravariantFunctor_obj_carrier (Y : (NonUnitalBimoduleCat.{uS, uR, uY} S R)ᵒᵖ) :
    ((homContravariantFunctor R hZ).obj Y).carrier = NonUnitalModuleHom S Y.unop Z := rfl

theorem homContravariantFunctor_map {Y Y' : (NonUnitalBimoduleCat.{uS, uR, uY} S R)ᵒᵖ}
    (f : Y ⟶ Y') :
    (homContravariantFunctor R hZ).map f =
      homMap Y.unop.actionsCommute Y'.unop.actionsCommute hZ hZ f.unop
        (NonUnitalBimoduleHom.id S T Z) := rfl

/-- The entire underlying additive map of a contravariant map is precomposition. -/
theorem homContravariantFunctor_map_val {Y Y' : (NonUnitalBimoduleCat.{uS, uR, uY} S R)ᵒᵖ}
    (f : Y ⟶ Y') :
    ((homContravariantFunctor R hZ).map f).val =
      precomposeAddHom (Z := Z) (NonUnitalBimoduleHom.toLeftHom f.unop) := rfl

end Contravariant

end Langlands.Algebra.NonUnitalBimoduleHomActions
