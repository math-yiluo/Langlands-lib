import Langlands.Algebra.NonUnitalBimoduleHomNaturality
import Langlands.Algebra.NondegenerateModuleAdditive
import Mathlib.CategoryTheory.Whiskering

/-!
# Actual fixed-source Hom and its nondegenerate part

Internal arbitrary-ring additive construction supporting Renard I.2.3.
The residual action, original maps and nondegenerate-part functor are reused.
-/

set_option autoImplicit false

open CategoryTheory MulOpposite

namespace Langlands.Algebra.NondegenerateHomFunctor

open NonUnitalBimoduleHomActions

universe uS uR uY uM uN uP

section Ambient

variable {S : Type uS} {R : Type uR} {Y : Type uY}
  [NonUnitalRing S] [NonUnitalRing R] [AddCommGroup Y]
  [NonUnitalModule S Y] [NonUnitalModule Rᵐᵒᵖ Y]
  (hY : ActionsCommute S R Y)
  {M : Type uM} {N : Type uN} {P : Type uP}
  [AddCommGroup M] [AddCommGroup N] [AddCommGroup P]
  [NonUnitalModule S M] [NonUnitalModule S N] [NonUnitalModule S P]

/-- The published one-sided map, with the identity on the fixed source. -/
abbrev ambientMap (f : NonUnitalModuleHom S M N) :
    NonUnitalModuleHom R (sourceHom hY M) (sourceHom hY N) :=
  sourceMap hY hY (NonUnitalBimoduleHom.id S R Y) f

theorem ambientMap_toAddMonoidHom (f : NonUnitalModuleHom S M N) :
    (ambientMap hY f).toAddMonoidHom = postcomposeAddHom (Y := Y) f := rfl

theorem ambientMap_apply (f : NonUnitalModuleHom S M N) (h : NonUnitalModuleHom S Y M) :
    ambientMap hY f h = f.comp h := rfl

theorem ambientMap_apply_apply (f : NonUnitalModuleHom S M N)
    (h : NonUnitalModuleHom S Y M) (y : Y) :
    (show NonUnitalModuleHom S Y N from ambientMap hY f h) y = f (h y) := rfl

theorem ambientMap_id : ambientMap hY (NonUnitalModuleHom.id S M) =
    NonUnitalModuleHom.id R (sourceHom hY M) := rfl

theorem ambientMap_comp (g : NonUnitalModuleHom S N P) (f : NonUnitalModuleHom S M N) :
    ambientMap hY (g.comp f) = (ambientMap hY g).comp (ambientMap hY f) := rfl

theorem ambientMap_add (f g : NonUnitalModuleHom S M N) :
    ambientMap hY (f + g) = ambientMap hY f + ambientMap hY g := by
  apply NonUnitalModuleHom.ext
  intro h
  apply NonUnitalModuleHom.ext
  intro y
  rfl

theorem ambientMap_zero : ambientMap hY (0 : NonUnitalModuleHom S M N) = 0 := by
  apply NonUnitalModuleHom.ext
  intro h
  apply NonUnitalModuleHom.ext
  intro y
  rfl

/-- No right action on the variable module is required. -/
def ambientFunctor :
    NonUnitalModuleCat.{uS, uM} S ⥤ NonUnitalModuleCat.{uR, max uY uM} R where
  obj M := sourceHom hY M
  map f := ambientMap hY f
  map_id _ := rfl
  map_comp _ _ := rfl

instance ambientFunctor_additive : (ambientFunctor.{uS, uR, uY, uM} hY).Additive where
  map_add := ambientMap_add hY _ _

theorem ambientFunctor_obj (M : NonUnitalModuleCat.{uS, uM} S) :
    (ambientFunctor hY).obj M = sourceHom hY M := rfl

theorem ambientFunctor_obj_carrier (M : NonUnitalModuleCat.{uS, uM} S) :
    ((ambientFunctor hY).obj M).carrier = NonUnitalModuleHom S Y M := rfl

theorem ambientFunctor_obj_group (M : NonUnitalModuleCat.{uS, uM} S) :
    ((ambientFunctor hY).obj M).isAddCommGroup =
      NonUnitalModuleHom.instAddCommGroup (A := S) (M := Y) (N := M) := rfl

theorem ambientFunctor_obj_action (M : NonUnitalModuleCat.{uS, uM} S) :
    ((ambientFunctor hY).obj M).isModule = sourceAction hY := rfl

theorem ambientFunctor_obj_toEndHom (M : NonUnitalModuleCat.{uS, uM} S) (r : R) :
    NonUnitalModule.toEndHom ((ambientFunctor hY).obj M).isModule r =
      precomposeAddHom (hY.rightActionHom (op r)) := rfl

theorem ambientFunctor_obj_smul (M : NonUnitalModuleCat.{uS, uM} S)
    (r : R) (h : (ambientFunctor hY).obj M) (y : Y) :
    (show NonUnitalModuleHom S Y M from r • h) y =
      (show NonUnitalModuleHom S Y M from h) (op r • y) := rfl

theorem ambientFunctor_map {M N : NonUnitalModuleCat.{uS, uM} S} (f : M ⟶ N) :
    (ambientFunctor hY).map f = ambientMap hY f := rfl

theorem ambientFunctor_map_toAddMonoidHom {M N : NonUnitalModuleCat.{uS, uM} S}
    (f : M ⟶ N) : ((ambientFunctor hY).map f).toAddMonoidHom = postcomposeAddHom f := rfl

theorem ambientFunctor_map_apply {M N : NonUnitalModuleCat.{uS, uM} S}
    (f : M ⟶ N) (h : (ambientFunctor hY).obj M) :
    (show NonUnitalModuleHom R (sourceHom hY M) (sourceHom hY N) from
      (ambientFunctor hY).map f) h = f.comp h := rfl

end Ambient

section Part

variable {S : Type uS} {R : Type uR} {Y : Type uY}
  [NonUnitalRing S] [NonUnitalRing R] [AddCommGroup Y]
  [NonUnitalModule S Y] [NonUnitalModule Rᵐᵒᵖ Y]
  (hY : ActionsCommute S R Y) (hR : IsIdempotented R)

/-- An abbreviation for the published part, with its named ambient action. -/
abbrev homPart (M : Type uM) [AddCommGroup M] [NonUnitalModule S M] :=
  nondegeneratePart hR (sourceHom hY M)

variable {M : Type uM} {N : Type uN} {P : Type uP}
  [AddCommGroup M] [AddCommGroup N] [AddCommGroup P]
  [NonUnitalModule S M] [NonUnitalModule S N] [NonUnitalModule S P]

theorem mem_homPart (h : NonUnitalModuleHom S Y M) :
    h ∈ homPart hY hR M ↔ ∃ e : Idempotent R,
      NonUnitalModule.toEndHom (sourceAction hY) (e : R) h = h := Iff.rfl

theorem mem_homPart_iff (h : NonUnitalModuleHom S Y M) :
    h ∈ homPart hY hR M ↔ ∃ e : Idempotent R, ∀ y : Y, h (op (e : R) • y) = h y := by
  constructor
  · rintro ⟨e, he⟩
    exact ⟨e, fun y => congrArg (fun k : NonUnitalModuleHom S Y M => k y) he⟩
  · rintro ⟨e, he⟩
    exact ⟨e, NonUnitalModuleHom.ext he⟩

/-- Restrict exactly the published one-sided postcomposition map. -/
abbrev partMap (f : NonUnitalModuleHom S M N) :
    NonUnitalModuleHom R (homPart hY hR M) (homPart hY hR N) :=
  (ambientMap hY f).restrictNondegeneratePart hR

theorem partMap_toAddMonoidHom (f : NonUnitalModuleHom S M N) :
    (partMap hY hR f).toAddMonoidHom =
      ((ambientMap hY f).restrictNondegeneratePart hR).toAddMonoidHom := rfl

theorem partMap_val (f : NonUnitalModuleHom S M N) (h : homPart hY hR M) :
    (partMap hY hR f h).val = f.comp h.val := rfl

theorem partMap_apply (f : NonUnitalModuleHom S M N) (h : homPart hY hR M) (y : Y) :
    (show NonUnitalModuleHom S Y N from (partMap hY hR f h).val) y =
      f ((show NonUnitalModuleHom S Y M from h.val) y) := rfl

theorem partMap_id : partMap hY hR (NonUnitalModuleHom.id S M) =
    NonUnitalModuleHom.id R (homPart hY hR M) :=
  NonUnitalModuleHom.restrictNondegeneratePart_id hR

theorem partMap_comp (g : NonUnitalModuleHom S N P) (f : NonUnitalModuleHom S M N) :
    partMap hY hR (g.comp f) = (partMap hY hR g).comp (partMap hY hR f) := by
  unfold partMap
  rw [ambientMap_comp]
  exact NonUnitalModuleHom.restrictNondegeneratePart_comp hR _ _

theorem partMap_add (f g : NonUnitalModuleHom S M N) :
    partMap hY hR (f + g) = partMap hY hR f + partMap hY hR g := by
  rw [partMap, ambientMap_add, NonUnitalModuleHom.restrictNondegeneratePart_add]

theorem partMap_zero : partMap hY hR (0 : NonUnitalModuleHom S M N) = 0 := by
  rw [partMap, ambientMap_zero, NonUnitalModuleHom.restrictNondegeneratePart_zero]

/-- Only the output ring is required to be idempotented. -/
def nondegenerateFunctor :
    NonUnitalModuleCat.{uS, uM} S ⥤ NondegenerateModuleCat.{uR, max uY uM} R :=
  ambientFunctor hY ⋙ nondegeneratePartFunctor hR

theorem nondegenerateFunctor_eq : nondegenerateFunctor.{uS, uR, uY, uM} hY hR =
    ambientFunctor hY ⋙ nondegeneratePartFunctor hR := rfl

instance nondegenerateFunctor_additive :
    (nondegenerateFunctor.{uS, uR, uY, uM} hY hR).Additive :=
  inferInstanceAs (ambientFunctor hY ⋙ nondegeneratePartFunctor hR).Additive

theorem nondegenerateFunctor_obj (M : NonUnitalModuleCat.{uS, uM} S) :
    (nondegenerateFunctor hY hR).obj M =
      ⟨NonUnitalModuleCat.of R (homPart hY hR M), nondegeneratePart_isNondegenerate hR⟩ := rfl

theorem nondegenerateFunctor_obj_carrier (M : NonUnitalModuleCat.{uS, uM} S) :
    ((nondegenerateFunctor hY hR).obj M).obj.carrier = homPart hY hR M := rfl

theorem nondegenerateFunctor_obj_group (M : NonUnitalModuleCat.{uS, uM} S) :
    ((nondegenerateFunctor hY hR).obj M).obj.isAddCommGroup =
      (inferInstance : AddCommGroup (homPart hY hR M)) := rfl

theorem nondegenerateFunctor_obj_action (M : NonUnitalModuleCat.{uS, uM} S) :
    ((nondegenerateFunctor hY hR).obj M).obj.isModule =
      (inferInstance : NonUnitalModule R (homPart hY hR M)) := rfl

theorem nondegenerateFunctor_obj_smul_val (M : NonUnitalModuleCat.{uS, uM} S)
    (r : R) (h : ((nondegenerateFunctor hY hR).obj M).obj) :
    (r • h).val = NonUnitalModule.toEndHom (sourceAction hY) r h.val := rfl

theorem nondegenerateFunctor_map {M N : NonUnitalModuleCat.{uS, uM} S} (f : M ⟶ N) :
    ((nondegenerateFunctor hY hR).map f).hom = partMap hY hR f := rfl

theorem nondegenerateFunctor_map_toAddMonoidHom {M N : NonUnitalModuleCat.{uS, uM} S}
    (f : M ⟶ N) : ((nondegenerateFunctor hY hR).map f).hom.toAddMonoidHom =
      ((ambientMap hY f).restrictNondegeneratePart hR).toAddMonoidHom := rfl

theorem nondegenerateFunctor_map_val {M N : NonUnitalModuleCat.{uS, uM} S}
    (f : M ⟶ N) (h : ((nondegenerateFunctor hY hR).obj M).obj) :
    ((show NonUnitalModuleHom R (homPart hY hR M) (homPart hY hR N) from
      ((nondegenerateFunctor hY hR).map f).hom) h).val = f.comp h.val := rfl

/-- The canonical inclusion is obtained by whiskering the published natural inclusion. -/
def inclusion : nondegenerateFunctor.{uS, uR, uY, uM} hY hR ⋙ nondegenerateInclusion R ⟶
    ambientFunctor hY :=
  Functor.whiskerLeft (ambientFunctor hY) (nondegeneratePartInclusion hR)

theorem inclusion_app (M : NonUnitalModuleCat.{uS, uM} S) :
    (inclusion hY hR).app M = (homPart hY hR M).subtype := rfl

theorem inclusion_app_toAddMonoidHom (M : NonUnitalModuleCat.{uS, uM} S) :
    ((inclusion hY hR).app M).toAddMonoidHom =
      (homPart hY hR M).toAddSubgroup.subtype := rfl

theorem inclusion_app_apply (M : NonUnitalModuleCat.{uS, uM} S)
    (h : ((nondegenerateFunctor hY hR).obj M).obj) :
    (show NonUnitalModuleHom R (homPart hY hR M) (sourceHom hY M) from
      (inclusion hY hR).app M) h = h.val := rfl

/-- Naturality as an equality of whole original `R`-linear maps. -/
theorem inclusion_naturality {M N : NonUnitalModuleCat.{uS, uM} S} (f : M ⟶ N) :
    (ambientMap hY f).comp ((homPart hY hR M).subtype) =
      ((homPart hY hR N).subtype).comp (partMap hY hR f) := by
  apply NonUnitalModuleHom.ext
  intro h
  rfl

/-- Restrict the input category, retaining the actual inclusion. -/
def restrictedFunctor :
    NondegenerateModuleCat.{uS, uM} S ⥤ NondegenerateModuleCat.{uR, max uY uM} R :=
  nondegenerateInclusion S ⋙ nondegenerateFunctor hY hR

theorem restrictedFunctor_eq : restrictedFunctor.{uS, uR, uY, uM} hY hR =
    nondegenerateInclusion S ⋙ (ambientFunctor hY ⋙ nondegeneratePartFunctor hR) := rfl

instance restrictedFunctor_additive :
    (restrictedFunctor.{uS, uR, uY, uM} hY hR).Additive :=
  inferInstanceAs (nondegenerateInclusion S ⋙ nondegenerateFunctor hY hR).Additive

theorem restrictedFunctor_obj (M : NondegenerateModuleCat.{uS, uM} S) :
    (restrictedFunctor hY hR).obj M = (nondegenerateFunctor hY hR).obj M.obj := rfl

theorem restrictedFunctor_map {M N : NondegenerateModuleCat.{uS, uM} S} (f : M ⟶ N) :
    ((restrictedFunctor hY hR).map f).hom = partMap hY hR f.hom := rfl

/-- Restrict the canonical inclusion by whiskering with the input inclusion. -/
def restrictedInclusion :
    restrictedFunctor.{uS, uR, uY, uM} hY hR ⋙ nondegenerateInclusion R ⟶
      nondegenerateInclusion S ⋙ ambientFunctor hY :=
  Functor.whiskerLeft (nondegenerateInclusion S) (inclusion hY hR)

theorem restrictedInclusion_app (M : NondegenerateModuleCat.{uS, uM} S) :
    (restrictedInclusion hY hR).app M = (homPart hY hR M.obj).subtype := rfl

theorem restrictedInclusion_app_toAddMonoidHom (M : NondegenerateModuleCat.{uS, uM} S) :
    ((restrictedInclusion hY hR).app M).toAddMonoidHom =
      (homPart hY hR M.obj).toAddSubgroup.subtype := rfl

end Part

end Langlands.Algebra.NondegenerateHomFunctor
