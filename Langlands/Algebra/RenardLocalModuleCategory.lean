import Langlands.Algebra.RenardModuleLocalization
import Mathlib.Algebra.Category.ModuleCat.Basic
import Mathlib.Algebra.Module.ULift
import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory
import Mathlib.CategoryTheory.Comma.StructuredArrow.Basic

/-! # The actual full subcategory of local modules and the canonical structured arrow -/

set_option autoImplicit false

noncomputable section

open CategoryTheory

namespace Langlands.Renard.ModuleLocalization

universe u v w

variable {R : Type u} [CommRing R] (S : Submonoid R)

/-- The existing locality condition as a property of actual bundled modules. -/
def localModuleProperty : ObjectProperty (ModuleCat.{v} R) :=
  fun N => IsSLocal S N

/-- The full subcategory of `R`-modules on which every denominator acts invertibly. -/
abbrev LocalModuleCat :=
  (localModuleProperty.{u, v} S).FullSubcategory

/-- Inclusion into modules over the original ring, retaining every linear map. -/
abbrev localModuleInclusion : LocalModuleCat.{u, v} S ⥤ ModuleCat.{v} R :=
  (localModuleProperty.{u, v} S).ι

/-- This is the fully faithful inclusion of the actual full subcategory. -/
abbrev localModuleInclusionFullyFaithful :
    (localModuleInclusion.{u, v} S).FullyFaithful :=
  (localModuleProperty.{u, v} S).fullyFaithfulι

/-- Explicit universe raising preserves exactly the existing locality condition. -/
theorem isSLocal_ulift_iff (N : Type v) [AddCommGroup N] [Module R N] :
    IsSLocal S (ULift.{w} N) ↔ IsSLocal S N := by
  rw [isSLocal_iff_bijective, isSLocal_iff_bijective]
  constructor
  · intro h s
    constructor
    · intro x y hxy
      have hxy' : (s : R) • (ULift.up x : ULift.{w} N) =
          (s : R) • (ULift.up y : ULift.{w} N) :=
        congrArg ULift.up hxy
      exact congrArg ULift.down ((h s).1 hxy')
    · intro x
      obtain ⟨y, hy⟩ := (h s).2 (ULift.up x)
      exact ⟨y.down, congrArg ULift.down hy⟩
  · intro h s
    constructor
    · intro x y hxy
      exact ULift.ext _ _ ((h s).1 (congrArg ULift.down hxy))
    · intro x
      obtain ⟨y, hy⟩ := (h s).2 x.down
      exact ⟨ULift.up y, ULift.ext _ _ hy⟩

variable (M : Type v) [AddCommGroup M] [Module R M]

/-- The source raised explicitly to the common ambient universe `max u v w`. -/
def raisedSource : ModuleCat.{max u v w} R :=
  ModuleCat.of R (ULift.{max u w} M)

/-- The actual localized module, raised explicitly into the same ambient universe. -/
def canonicalLocalObject : LocalModuleCat.{u, max u v w} S :=
  ⟨ModuleCat.of R (ULift.{w} (LocalizedModule S M)),
    (isSLocal_ulift_iff S (LocalizedModule S M)).2 (localizedModule_isSLocal S)⟩

/-- The actual canonical localization map transported along the two explicit lifts. -/
def canonicalModuleMap :
    raisedSource.{u, v, w} (R := R) M ⟶
      (localModuleInclusion.{u, max u v w} S).obj
        (canonicalLocalObject.{u, v, w} S M) :=
  ModuleCat.ofHom <|
    (ULift.moduleEquiv (R := R) (M := LocalizedModule S M)).symm.toLinearMap.comp
      ((LocalizedModule.mkLinearMap S M).comp (ULift.moduleEquiv (R := R) (M := M)).toLinearMap)

/-- The canonical candidate for the source's right universal arrow.
Initiality is a separate statement and proof obligation. -/
def canonicalStructuredArrow :
    StructuredArrow (raisedSource.{u, v, w} (R := R) M)
      (localModuleInclusion.{u, max u v w} S) :=
  StructuredArrow.mk (canonicalModuleMap.{u, v, w} S M)

/-- On a raised vector the canonical arrow is precisely the raised actual map. -/
@[simp] theorem canonicalModuleMap_up (m : M) :
    canonicalModuleMap.{u, v, w} S M (ULift.up m) =
      ULift.up (LocalizedModule.mkLinearMap S M m) :=
  rfl

/-- The pointwise factor candidate uses the published lift into the actual target.
Its categorical universal property is not assumed as input. -/
def canonicalFactor (N : LocalModuleCat.{u, max u v w} S)
    (f : raisedSource.{u, v, w} (R := R) M ⟶ N.obj) :
    canonicalLocalObject.{u, v, w} S M ⟶ N :=
  ObjectProperty.homMk <| ModuleCat.ofHom <|
    (factor S N.property
      (f.hom.comp (ULift.moduleEquiv (R := R) (M := M)).symm.toLinearMap)).comp
        (ULift.moduleEquiv (R := R) (M := LocalizedModule S M)).toLinearMap

/-- The factor candidate is the existing linear factor after removing the localization-source lift. -/
theorem canonicalFactor_apply (N : LocalModuleCat.{u, max u v w} S)
    (f : raisedSource.{u, v, w} (R := R) M ⟶ N.obj)
    (z : ULift.{w} (LocalizedModule S M)) :
    (canonicalFactor.{u, v, w} S M N f).hom z =
      factor S N.property
        (f.hom.comp (ULift.moduleEquiv (R := R) (M := M)).symm.toLinearMap) z.down :=
  rfl

/-- The actual target still represents the zero module when zero is a denominator. -/
theorem canonicalLocalObject_subsingleton (h0 : (0 : R) ∈ S) :
    Subsingleton (canonicalLocalObject.{u, v, w} S M).obj := by
  change Subsingleton (ULift.{w} (LocalizedModule S M))
  let : Subsingleton (LocalizedModule S M) := localizedModule_subsingleton S h0
  infer_instance

end Langlands.Renard.ModuleLocalization
