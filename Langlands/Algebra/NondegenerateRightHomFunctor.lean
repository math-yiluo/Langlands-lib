import Langlands.Algebra.NonUnitalBimoduleHomNaturality
import Langlands.Algebra.NondegenerateModuleAdditive
import Langlands.Algebra.NonUnitalModuleDualFixedPartMaps
import Mathlib.CategoryTheory.Whiskering

/-!
# Actual right-module fixed-source Hom and its nondegenerate part

Internal arbitrary-ring additive construction supporting Renard I.2.3 and the right-module adaptations in I.4.2.
The residual action, original maps and nondegenerate-part functor are reused.
-/

set_option autoImplicit false

open CategoryTheory MulOpposite

namespace Langlands.Algebra.NondegenerateRightHomFunctor

open NonUnitalBimoduleHomActions

universe uS uR uY uM uN uP

section Ambient

variable {S : Type uS} {R : Type uR} {Y : Type uY}
  [NonUnitalRing S] [NonUnitalRing R] [AddCommGroup Y]
  [NonUnitalModule R Y] [NonUnitalModule Sᵐᵒᵖ Y]
  (hY : ActionsCommute R S Y)
  {M : Type uM} {N : Type uN} {P : Type uP}
  [AddCommGroup M] [AddCommGroup N] [AddCommGroup P]
  [NonUnitalModule Sᵐᵒᵖ M] [NonUnitalModule Sᵐᵒᵖ N] [NonUnitalModule Sᵐᵒᵖ P]

/-- The published one-sided map, with the identity on the fixed source. -/
abbrev ambientMap (f : NonUnitalModuleHom Sᵐᵒᵖ M N) :
    NonUnitalModuleHom Rᵐᵒᵖ (rightSourceHom hY M) (rightSourceHom hY N) :=
  rightSourceMap hY hY (NonUnitalBimoduleHom.id R S Y) f

theorem ambientMap_toAddMonoidHom (f : NonUnitalModuleHom Sᵐᵒᵖ M N) :
    (ambientMap hY f).toAddMonoidHom = postcomposeAddHom (Y := Y) f := rfl

theorem ambientMap_apply (f : NonUnitalModuleHom Sᵐᵒᵖ M N) (h : NonUnitalModuleHom Sᵐᵒᵖ Y M) :
    ambientMap hY f h = f.comp h := rfl

theorem ambientMap_apply_apply (f : NonUnitalModuleHom Sᵐᵒᵖ M N)
    (h : NonUnitalModuleHom Sᵐᵒᵖ Y M) (y : Y) :
    (show NonUnitalModuleHom Sᵐᵒᵖ Y N from ambientMap hY f h) y = f (h y) := rfl

theorem ambientMap_id : ambientMap hY (NonUnitalModuleHom.id Sᵐᵒᵖ M) =
    NonUnitalModuleHom.id Rᵐᵒᵖ (rightSourceHom hY M) := rfl

theorem ambientMap_comp (g : NonUnitalModuleHom Sᵐᵒᵖ N P) (f : NonUnitalModuleHom Sᵐᵒᵖ M N) :
    ambientMap hY (g.comp f) = (ambientMap hY g).comp (ambientMap hY f) := rfl

theorem ambientMap_add (f g : NonUnitalModuleHom Sᵐᵒᵖ M N) :
    ambientMap hY (f + g) = ambientMap hY f + ambientMap hY g := by
  apply NonUnitalModuleHom.ext
  intro h
  apply NonUnitalModuleHom.ext
  intro y
  rfl

theorem ambientMap_zero : ambientMap hY (0 : NonUnitalModuleHom Sᵐᵒᵖ M N) = 0 := by
  apply NonUnitalModuleHom.ext
  intro h
  apply NonUnitalModuleHom.ext
  intro y
  rfl

/-- Only the original right `S`-action on the variable module is required. -/
def ambientFunctor :
    NonUnitalModuleCat.{uS, uM} Sᵐᵒᵖ ⥤ NonUnitalModuleCat.{uR, max uY uM} Rᵐᵒᵖ where
  obj M := rightSourceHom hY M
  map f := ambientMap hY f
  map_id _ := rfl
  map_comp _ _ := rfl

instance ambientFunctor_additive : (ambientFunctor.{uS, uR, uY, uM} hY).Additive where
  map_add := ambientMap_add hY _ _

theorem ambientFunctor_obj (M : NonUnitalModuleCat.{uS, uM} Sᵐᵒᵖ) :
    (ambientFunctor hY).obj M = rightSourceHom hY M := rfl

theorem ambientFunctor_obj_carrier (M : NonUnitalModuleCat.{uS, uM} Sᵐᵒᵖ) :
    ((ambientFunctor hY).obj M).carrier = NonUnitalModuleHom Sᵐᵒᵖ Y M := rfl

theorem ambientFunctor_obj_group (M : NonUnitalModuleCat.{uS, uM} Sᵐᵒᵖ) :
    ((ambientFunctor hY).obj M).isAddCommGroup =
      NonUnitalModuleHom.instAddCommGroup (A := Sᵐᵒᵖ) (M := Y) (N := M) := rfl

theorem ambientFunctor_obj_action (M : NonUnitalModuleCat.{uS, uM} Sᵐᵒᵖ) :
    ((ambientFunctor hY).obj M).isModule = rightSourceAction hY := rfl

theorem ambientFunctor_obj_toEndHom (M : NonUnitalModuleCat.{uS, uM} Sᵐᵒᵖ) (r : R) :
    NonUnitalModule.toEndHom ((ambientFunctor hY).obj M).isModule (op r) =
      precomposeAddHom (hY.leftActionHom r) := rfl

theorem ambientFunctor_obj_smul (M : NonUnitalModuleCat.{uS, uM} Sᵐᵒᵖ)
    (r : R) (h : (ambientFunctor hY).obj M) (y : Y) :
    (show NonUnitalModuleHom Sᵐᵒᵖ Y M from op r • h) y =
      (show NonUnitalModuleHom Sᵐᵒᵖ Y M from h) (r • y) := rfl

theorem ambientFunctor_map {M N : NonUnitalModuleCat.{uS, uM} Sᵐᵒᵖ} (f : M ⟶ N) :
    (ambientFunctor hY).map f = ambientMap hY f := rfl

theorem ambientFunctor_map_toAddMonoidHom {M N : NonUnitalModuleCat.{uS, uM} Sᵐᵒᵖ}
    (f : M ⟶ N) : ((ambientFunctor hY).map f).toAddMonoidHom = postcomposeAddHom f := rfl

theorem ambientFunctor_map_apply {M N : NonUnitalModuleCat.{uS, uM} Sᵐᵒᵖ}
    (f : M ⟶ N) (h : (ambientFunctor hY).obj M) :
    (show NonUnitalModuleHom Rᵐᵒᵖ (rightSourceHom hY M) (rightSourceHom hY N) from
      (ambientFunctor hY).map f) h = f.comp h := rfl

end Ambient

section Part

variable {S : Type uS} {R : Type uR} {Y : Type uY}
  [NonUnitalRing S] [NonUnitalRing R] [AddCommGroup Y]
  [NonUnitalModule R Y] [NonUnitalModule Sᵐᵒᵖ Y]
  (hY : ActionsCommute R S Y) (hR : IsIdempotented R)

/-- An abbreviation for the published part, with its named ambient action. -/
abbrev homPart (M : Type uM) [AddCommGroup M] [NonUnitalModule Sᵐᵒᵖ M] :=
  nondegeneratePart hR.op (rightSourceHom hY M)

variable {M : Type uM} {N : Type uN} {P : Type uP}
  [AddCommGroup M] [AddCommGroup N] [AddCommGroup P]
  [NonUnitalModule Sᵐᵒᵖ M] [NonUnitalModule Sᵐᵒᵖ N] [NonUnitalModule Sᵐᵒᵖ P]

theorem mem_homPart (h : NonUnitalModuleHom Sᵐᵒᵖ Y M) :
    h ∈ homPart hY hR M ↔ ∃ e : Idempotent Rᵐᵒᵖ,
      NonUnitalModule.toEndHom (rightSourceAction hY) (e : Rᵐᵒᵖ) h = h := Iff.rfl

theorem mem_homPart_iff (h : NonUnitalModuleHom Sᵐᵒᵖ Y M) :
    h ∈ homPart hY hR M ↔ ∃ e : Idempotent R, ∀ y : Y, h ((e : R) • y) = h y := by
  constructor
  · rintro ⟨e, he⟩
    let e' : Idempotent R := ⟨(e : Rᵐᵒᵖ).unop, by
      exact congrArg MulOpposite.unop e.property.eq⟩
    exact ⟨e', fun y => congrArg (fun k : NonUnitalModuleHom Sᵐᵒᵖ Y M => k y) he⟩
  · rintro ⟨e, he⟩
    exact ⟨NonUnitalModuleDualFixedPartMaps.oppositeIdempotent e,
      NonUnitalModuleHom.ext he⟩

/-- Restrict exactly the published one-sided postcomposition map. -/
abbrev partMap (f : NonUnitalModuleHom Sᵐᵒᵖ M N) :
    NonUnitalModuleHom Rᵐᵒᵖ (homPart hY hR M) (homPart hY hR N) :=
  (ambientMap hY f).restrictNondegeneratePart hR.op

theorem partMap_toAddMonoidHom (f : NonUnitalModuleHom Sᵐᵒᵖ M N) :
    (partMap hY hR f).toAddMonoidHom =
      ((ambientMap hY f).restrictNondegeneratePart hR.op).toAddMonoidHom := rfl

theorem partMap_val (f : NonUnitalModuleHom Sᵐᵒᵖ M N) (h : homPart hY hR M) :
    (partMap hY hR f h).val = f.comp h.val := rfl

theorem partMap_apply (f : NonUnitalModuleHom Sᵐᵒᵖ M N) (h : homPart hY hR M) (y : Y) :
    (show NonUnitalModuleHom Sᵐᵒᵖ Y N from (partMap hY hR f h).val) y =
      f ((show NonUnitalModuleHom Sᵐᵒᵖ Y M from h.val) y) := rfl

theorem partMap_id : partMap hY hR (NonUnitalModuleHom.id Sᵐᵒᵖ M) =
    NonUnitalModuleHom.id Rᵐᵒᵖ (homPart hY hR M) :=
  NonUnitalModuleHom.restrictNondegeneratePart_id hR.op

theorem partMap_comp (g : NonUnitalModuleHom Sᵐᵒᵖ N P) (f : NonUnitalModuleHom Sᵐᵒᵖ M N) :
    partMap hY hR (g.comp f) = (partMap hY hR g).comp (partMap hY hR f) := by
  unfold partMap
  rw [ambientMap_comp]
  exact NonUnitalModuleHom.restrictNondegeneratePart_comp hR.op _ _

theorem partMap_add (f g : NonUnitalModuleHom Sᵐᵒᵖ M N) :
    partMap hY hR (f + g) = partMap hY hR f + partMap hY hR g := by
  rw [partMap, ambientMap_add, NonUnitalModuleHom.restrictNondegeneratePart_add]

theorem partMap_zero : partMap hY hR (0 : NonUnitalModuleHom Sᵐᵒᵖ M N) = 0 := by
  rw [partMap, ambientMap_zero, NonUnitalModuleHom.restrictNondegeneratePart_zero]

/-- Only the output ring is required to be idempotented. -/
def nondegenerateFunctor :
    NonUnitalModuleCat.{uS, uM} Sᵐᵒᵖ ⥤ NondegenerateModuleCat.{uR, max uY uM} Rᵐᵒᵖ :=
  ambientFunctor hY ⋙ nondegeneratePartFunctor hR.op

theorem nondegenerateFunctor_eq : nondegenerateFunctor.{uS, uR, uY, uM} hY hR =
    ambientFunctor hY ⋙ nondegeneratePartFunctor hR.op := rfl

instance nondegenerateFunctor_additive :
    (nondegenerateFunctor.{uS, uR, uY, uM} hY hR).Additive :=
  inferInstanceAs (ambientFunctor hY ⋙ nondegeneratePartFunctor hR.op).Additive

theorem nondegenerateFunctor_obj (M : NonUnitalModuleCat.{uS, uM} Sᵐᵒᵖ) :
    (nondegenerateFunctor hY hR).obj M =
      ⟨NonUnitalModuleCat.of Rᵐᵒᵖ (homPart hY hR M), nondegeneratePart_isNondegenerate hR.op⟩ := rfl

theorem nondegenerateFunctor_obj_carrier (M : NonUnitalModuleCat.{uS, uM} Sᵐᵒᵖ) :
    ((nondegenerateFunctor hY hR).obj M).obj.carrier = homPart hY hR M := rfl

theorem nondegenerateFunctor_obj_group (M : NonUnitalModuleCat.{uS, uM} Sᵐᵒᵖ) :
    ((nondegenerateFunctor hY hR).obj M).obj.isAddCommGroup =
      (inferInstanceAs (AddCommGroup (homPart hY hR M).toAddSubgroup)) := rfl

theorem nondegenerateFunctor_obj_action (M : NonUnitalModuleCat.{uS, uM} Sᵐᵒᵖ) :
    ((nondegenerateFunctor hY hR).obj M).obj.isModule =
      (homPart hY hR M).instNonUnitalModuleSubtypeMem := rfl

theorem nondegenerateFunctor_obj_smul_val (M : NonUnitalModuleCat.{uS, uM} Sᵐᵒᵖ)
    (r : R) (h : ((nondegenerateFunctor hY hR).obj M).obj) :
    (op r • h).val = NonUnitalModule.toEndHom (rightSourceAction hY) (op r) h.val := rfl

theorem nondegenerateFunctor_map {M N : NonUnitalModuleCat.{uS, uM} Sᵐᵒᵖ} (f : M ⟶ N) :
    ((nondegenerateFunctor hY hR).map f).hom = partMap hY hR f := rfl

theorem nondegenerateFunctor_map_toAddMonoidHom {M N : NonUnitalModuleCat.{uS, uM} Sᵐᵒᵖ}
    (f : M ⟶ N) : ((nondegenerateFunctor hY hR).map f).hom.toAddMonoidHom =
      ((ambientMap hY f).restrictNondegeneratePart hR.op).toAddMonoidHom := rfl

theorem nondegenerateFunctor_map_val {M N : NonUnitalModuleCat.{uS, uM} Sᵐᵒᵖ}
    (f : M ⟶ N) (h : ((nondegenerateFunctor hY hR).obj M).obj) :
    ((show NonUnitalModuleHom Rᵐᵒᵖ (homPart hY hR M) (homPart hY hR N) from
      ((nondegenerateFunctor hY hR).map f).hom) h).val = f.comp h.val := rfl

/-- The canonical inclusion is obtained by whiskering the published natural inclusion. -/
def inclusion : nondegenerateFunctor.{uS, uR, uY, uM} hY hR ⋙ nondegenerateInclusion Rᵐᵒᵖ ⟶
    ambientFunctor hY :=
  Functor.whiskerLeft (ambientFunctor hY) (nondegeneratePartInclusion hR.op)

theorem inclusion_app (M : NonUnitalModuleCat.{uS, uM} Sᵐᵒᵖ) :
    (inclusion hY hR).app M = (homPart hY hR M).subtype := rfl

theorem inclusion_app_toAddMonoidHom (M : NonUnitalModuleCat.{uS, uM} Sᵐᵒᵖ) :
    ((inclusion hY hR).app M).toAddMonoidHom =
      (homPart hY hR M).toAddSubgroup.subtype := rfl

theorem inclusion_app_apply (M : NonUnitalModuleCat.{uS, uM} Sᵐᵒᵖ)
    (h : ((nondegenerateFunctor hY hR).obj M).obj) :
    (show NonUnitalModuleHom Rᵐᵒᵖ (homPart hY hR M) (rightSourceHom hY M) from
      (inclusion hY hR).app M) h = h.val := rfl

/-- Naturality as an equality of whole original right-`R`-linear maps. -/
theorem inclusion_naturality {M : Type uM} {N : Type uN}
    [AddCommGroup M] [AddCommGroup N]
    [NonUnitalModule Sᵐᵒᵖ M] [NonUnitalModule Sᵐᵒᵖ N]
    (f : NonUnitalModuleHom Sᵐᵒᵖ M N) :
    (ambientMap hY f).comp ((homPart hY hR M).subtype) =
      ((homPart hY hR N).subtype).comp (partMap hY hR f) := by
  apply NonUnitalModuleHom.ext
  intro h
  rfl

/-- Restrict the input category, retaining the actual inclusion. -/
def restrictedFunctor :
    NondegenerateModuleCat.{uS, uM} Sᵐᵒᵖ ⥤ NondegenerateModuleCat.{uR, max uY uM} Rᵐᵒᵖ :=
  nondegenerateInclusion Sᵐᵒᵖ ⋙ nondegenerateFunctor hY hR

theorem restrictedFunctor_eq : restrictedFunctor.{uS, uR, uY, uM} hY hR =
    nondegenerateInclusion Sᵐᵒᵖ ⋙ (ambientFunctor hY ⋙ nondegeneratePartFunctor hR.op) := rfl

instance restrictedFunctor_additive :
    (restrictedFunctor.{uS, uR, uY, uM} hY hR).Additive :=
  inferInstanceAs (nondegenerateInclusion Sᵐᵒᵖ ⋙ nondegenerateFunctor hY hR).Additive

theorem restrictedFunctor_obj (M : NondegenerateModuleCat.{uS, uM} Sᵐᵒᵖ) :
    (restrictedFunctor hY hR).obj M = (nondegenerateFunctor hY hR).obj M.obj := rfl

theorem restrictedFunctor_map {M N : NondegenerateModuleCat.{uS, uM} Sᵐᵒᵖ} (f : M ⟶ N) :
    ((restrictedFunctor hY hR).map f).hom = partMap hY hR f.hom := rfl

/-- Restrict the canonical inclusion by whiskering with the input inclusion. -/
def restrictedInclusion :
    restrictedFunctor.{uS, uR, uY, uM} hY hR ⋙ nondegenerateInclusion Rᵐᵒᵖ ⟶
      nondegenerateInclusion Sᵐᵒᵖ ⋙ ambientFunctor hY :=
  Functor.whiskerLeft (nondegenerateInclusion Sᵐᵒᵖ) (inclusion hY hR)

theorem restrictedInclusion_app (M : NondegenerateModuleCat.{uS, uM} Sᵐᵒᵖ) :
    (restrictedInclusion hY hR).app M = (homPart hY hR M.obj).subtype := rfl

theorem restrictedInclusion_app_toAddMonoidHom (M : NondegenerateModuleCat.{uS, uM} Sᵐᵒᵖ) :
    ((restrictedInclusion hY hR).app M).toAddMonoidHom =
      (homPart hY hR M.obj).toAddSubgroup.subtype := rfl

theorem restrictedInclusion_app_apply (M : NondegenerateModuleCat.{uS, uM} Sᵐᵒᵖ)
    (h : ((restrictedFunctor hY hR).obj M).obj) :
    (show NonUnitalModuleHom Rᵐᵒᵖ (homPart hY hR M.obj) (rightSourceHom hY M.obj) from
      (restrictedInclusion hY hR).app M) h = h.val := rfl

theorem restrictedInclusion_naturality {M N : NondegenerateModuleCat.{uS, uM} Sᵐᵒᵖ}
    (f : M ⟶ N) :
    (ambientMap hY f.hom).comp (homPart hY hR M.obj).subtype =
      (homPart hY hR N.obj).subtype.comp (partMap hY hR f.hom) :=
  inclusion_naturality hY hR f.hom

end Part

end Langlands.Algebra.NondegenerateRightHomFunctor
