import Langlands.Algebra.NondegenerateRightHomFunctor

/-!
# Renard's right-module pseudo-forgetful functor and induction

Direct original-Hom specializations of the actual nondegenerate Hom composite.
The two regular actions on the original carrier B are selected explicitly.
-/

set_option autoImplicit false

open CategoryTheory MulOpposite

namespace Langlands.Algebra.RenardRightHomFunctors

open NonUnitalBimoduleHomActions NondegenerateRightHomFunctor

universe uA uB uM uN

section Pseudo

variable {A : Type uA} {B : Type uB} [NonUnitalRing A] [NonUnitalRing B]
  [hLeft : NonUnitalModule A B]

local instance pseudoSourceRight : NonUnitalModule Bᵐᵒᵖ B :=
  NonUnitalModule.rightRegular B

variable (hAB : ActionsCommute A B B) (hA : IsIdempotented A)
  {M : Type uM} {N : Type uN} [AddCommGroup M] [AddCommGroup N]
  [NonUnitalModule Bᵐᵒᵖ M] [NonUnitalModule Bᵐᵒᵖ N]

/-- The named original residual action on the actual regular-source Hom. -/
abbrev rightPseudoAction : NonUnitalModule Aᵐᵒᵖ (NonUnitalModuleHom Bᵐᵒᵖ B M) :=
  rightSourceAction hAB

theorem rightPseudoAction_eq : rightPseudoAction (M := M) hAB =
    rightSourceAction hAB := rfl

theorem rightPseudoAction_toEndHom (a : A) :
    NonUnitalModule.toEndHom (rightPseudoAction (M := M) hAB) (op a) =
      precomposeAddHom (hAB.leftActionHom a) := rfl

theorem rightPseudoAction_smul (a : A) (φ : NonUnitalModuleHom Bᵐᵒᵖ B M) (b : B) :
    NonUnitalModule.toEndHom (rightPseudoAction hAB) (op a) φ b = φ (a • b) := rfl

/-- The actual `A.op`-part for the supplied left `A`-action on the original `B`. -/
abbrev rightPseudoPart (M : Type uM) [AddCommGroup M] [NonUnitalModule Bᵐᵒᵖ M] :=
  homPart hAB hA M

theorem mem_rightPseudoPart (φ : NonUnitalModuleHom Bᵐᵒᵖ B M) :
    φ ∈ rightPseudoPart hAB hA M ↔
      ∃ e : Idempotent A, ∀ b : B, φ ((e : A) • b) = φ b :=
  mem_homPart_iff hAB hA φ

abbrev rightPseudoMap (f : NonUnitalModuleHom Bᵐᵒᵖ M N) :
    NonUnitalModuleHom Aᵐᵒᵖ (rightPseudoPart hAB hA M) (rightPseudoPart hAB hA N) :=
  partMap hAB hA f

theorem rightPseudoMap_eq (f : NonUnitalModuleHom Bᵐᵒᵖ M N) :
    rightPseudoMap hAB hA f = (ambientMap hAB f).restrictNondegeneratePart hA.op := rfl

theorem rightPseudoMap_toAddMonoidHom (f : NonUnitalModuleHom Bᵐᵒᵖ M N) :
    (rightPseudoMap hAB hA f).toAddMonoidHom =
      ((ambientMap hAB f).restrictNondegeneratePart hA.op).toAddMonoidHom := rfl

theorem rightPseudoMap_val (f : NonUnitalModuleHom Bᵐᵒᵖ M N) (φ : rightPseudoPart hAB hA M) :
    (rightPseudoMap hAB hA f φ).val = f.comp φ.val := rfl

theorem rightPseudoMap_apply (f : NonUnitalModuleHom Bᵐᵒᵖ M N)
    (φ : rightPseudoPart hAB hA M) (b : B) :
    (show NonUnitalModuleHom Bᵐᵒᵖ B N from (rightPseudoMap hAB hA f φ).val) b =
      f ((show NonUnitalModuleHom Bᵐᵒᵖ B M from φ.val) b) := rfl

/-- The right-module additive pseudo-forgetful functor invoked in I.4.2. -/
def rightPseudoF : NondegenerateModuleCat.{uB, uM} Bᵐᵒᵖ ⥤
    NondegenerateModuleCat.{uA, max uB uM} Aᵐᵒᵖ :=
  restrictedFunctor hAB hA

theorem rightPseudoF_eq : rightPseudoF.{uA, uB, uM} hAB hA = restrictedFunctor hAB hA := rfl

theorem rightPseudoF_eq_composite : rightPseudoF.{uA, uB, uM} hAB hA =
    nondegenerateInclusion Bᵐᵒᵖ ⋙ (ambientFunctor hAB ⋙ nondegeneratePartFunctor hA.op) := rfl

instance rightPseudoF_additive : (rightPseudoF.{uA, uB, uM} hAB hA).Additive :=
  inferInstanceAs (restrictedFunctor hAB hA).Additive

theorem rightPseudoF_obj (M : NondegenerateModuleCat.{uB, uM} Bᵐᵒᵖ) :
    (rightPseudoF hAB hA).obj M =
      ⟨NonUnitalModuleCat.of Aᵐᵒᵖ (rightPseudoPart hAB hA M.obj),
        nondegeneratePart_isNondegenerate hA.op⟩ := rfl

theorem rightPseudoF_obj_carrier (M : NondegenerateModuleCat.{uB, uM} Bᵐᵒᵖ) :
    ((rightPseudoF hAB hA).obj M).obj.carrier = rightPseudoPart hAB hA M.obj := rfl

theorem rightPseudoF_obj_group (M : NondegenerateModuleCat.{uB, uM} Bᵐᵒᵖ) :
    ((rightPseudoF hAB hA).obj M).obj.isAddCommGroup =
      (inferInstanceAs (AddCommGroup (rightPseudoPart hAB hA M.obj).toAddSubgroup)) := rfl

theorem rightPseudoF_obj_action (M : NondegenerateModuleCat.{uB, uM} Bᵐᵒᵖ) :
    ((rightPseudoF hAB hA).obj M).obj.isModule =
      (rightPseudoPart hAB hA M.obj).instNonUnitalModuleSubtypeMem := rfl

theorem rightPseudoF_obj_smul_val (M : NondegenerateModuleCat.{uB, uM} Bᵐᵒᵖ)
    (a : A) (φ : ((rightPseudoF hAB hA).obj M).obj) :
    (op a • φ).val = NonUnitalModule.toEndHom (rightPseudoAction hAB) (op a) φ.val := rfl

theorem rightPseudoF_obj_smul_apply (M : NondegenerateModuleCat.{uB, uM} Bᵐᵒᵖ)
    (a : A) (φ : ((rightPseudoF hAB hA).obj M).obj) (b : B) :
    (show NonUnitalModuleHom Bᵐᵒᵖ B M.obj from (op a • φ).val) b =
      (show NonUnitalModuleHom Bᵐᵒᵖ B M.obj from φ.val) (a • b) := rfl

theorem rightPseudoF_map {M N : NondegenerateModuleCat.{uB, uM} Bᵐᵒᵖ} (f : M ⟶ N) :
    ((rightPseudoF hAB hA).map f).hom = (ambientMap hAB f.hom).restrictNondegeneratePart hA.op := rfl

theorem rightPseudoF_map_toAddMonoidHom {M N : NondegenerateModuleCat.{uB, uM} Bᵐᵒᵖ}
    (f : M ⟶ N) :
    ((rightPseudoF hAB hA).map f).hom.toAddMonoidHom =
      ((ambientMap hAB f.hom).restrictNondegeneratePart hA.op).toAddMonoidHom := rfl

theorem rightPseudoF_map_val {M N : NondegenerateModuleCat.{uB, uM} Bᵐᵒᵖ} (f : M ⟶ N)
    (φ : ((rightPseudoF hAB hA).obj M).obj) :
    ((show NonUnitalModuleHom Aᵐᵒᵖ (rightPseudoPart hAB hA M.obj) (rightPseudoPart hAB hA N.obj) from
      ((rightPseudoF hAB hA).map f).hom) φ).val = f.hom.comp φ.val := rfl

theorem rightPseudoF_map_apply {M N : NondegenerateModuleCat.{uB, uM} Bᵐᵒᵖ} (f : M ⟶ N)
    (φ : ((rightPseudoF hAB hA).obj M).obj) (b : B) :
    (show NonUnitalModuleHom Bᵐᵒᵖ B N.obj from
      ((show NonUnitalModuleHom Aᵐᵒᵖ (rightPseudoPart hAB hA M.obj) (rightPseudoPart hAB hA N.obj) from
        ((rightPseudoF hAB hA).map f).hom) φ).val) b =
      (show NonUnitalModuleHom Bᵐᵒᵖ M.obj N.obj from f.hom)
        ((show NonUnitalModuleHom Bᵐᵒᵖ B M.obj from φ.val) b) := rfl

def rightPseudoInclusion : rightPseudoF.{uA, uB, uM} hAB hA ⋙ nondegenerateInclusion Aᵐᵒᵖ ⟶
    nondegenerateInclusion Bᵐᵒᵖ ⋙ ambientFunctor hAB :=
  restrictedInclusion hAB hA

theorem rightPseudoInclusion_eq : rightPseudoInclusion.{uA, uB, uM} hAB hA =
    restrictedInclusion hAB hA := rfl

theorem rightPseudoInclusion_app (M : NondegenerateModuleCat.{uB, uM} Bᵐᵒᵖ) :
    (rightPseudoInclusion hAB hA).app M = (rightPseudoPart hAB hA M.obj).subtype := rfl

theorem rightPseudoInclusion_app_toAddMonoidHom (M : NondegenerateModuleCat.{uB, uM} Bᵐᵒᵖ) :
    ((rightPseudoInclusion hAB hA).app M).toAddMonoidHom =
      (rightPseudoPart hAB hA M.obj).toAddSubgroup.subtype := rfl

theorem rightPseudoInclusion_app_apply (M : NondegenerateModuleCat.{uB, uM} Bᵐᵒᵖ)
    (φ : ((rightPseudoF hAB hA).obj M).obj) :
    (show NonUnitalModuleHom Aᵐᵒᵖ (rightPseudoPart hAB hA M.obj) (rightSourceHom hAB M.obj) from
      (rightPseudoInclusion hAB hA).app M) φ = φ.val := rfl

theorem rightPseudoInclusion_naturality {M N : NondegenerateModuleCat.{uB, uM} Bᵐᵒᵖ} (f : M ⟶ N) :
    (ambientMap hAB f.hom).comp (rightPseudoPart hAB hA M.obj).subtype =
      (rightPseudoPart hAB hA N.obj).subtype.comp (rightPseudoMap hAB hA f.hom) :=
  inclusion_naturality hAB hA f.hom

/-- Adapter for Renard's two-sided nondegeneracy assumption on the specified bimodule. -/
abbrev rightPseudoFOfNondegenerate (_hBim : IsNondegenerateBimodule A B B) :
    NondegenerateModuleCat.{uB, uM} Bᵐᵒᵖ ⥤ NondegenerateModuleCat.{uA, max uB uM} Aᵐᵒᵖ :=
  rightPseudoF hAB hA

theorem rightPseudoFOfNondegenerate_eq (hBim : IsNondegenerateBimodule A B B) :
    rightPseudoFOfNondegenerate.{uA, uB, uM} hAB hA hBim = rightPseudoF hAB hA := rfl

end Pseudo

section Induction

variable {A : Type uA} {B : Type uB} [NonUnitalRing A] [NonUnitalRing B]
  [hRight : NonUnitalModule Aᵐᵒᵖ B]

local instance inductionSourceLeft : NonUnitalModule B B :=
  NonUnitalModule.regular B

variable (hBA : ActionsCommute B A B) (hB : IsIdempotented B)
  {M : Type uM} {N : Type uN} [AddCommGroup M] [AddCommGroup N]
  [NonUnitalModule Aᵐᵒᵖ M] [NonUnitalModule Aᵐᵒᵖ N]

/-- The named right-source action using exactly the left regular action of `B`. -/
abbrev rightInductionAction : NonUnitalModule Bᵐᵒᵖ (NonUnitalModuleHom Aᵐᵒᵖ B M) :=
  rightSourceAction hBA

theorem rightInductionAction_eq : rightInductionAction (M := M) hBA =
    rightSourceAction hBA := rfl

theorem rightInductionAction_toEndHom (b : B) :
    NonUnitalModule.toEndHom (rightInductionAction (M := M) hBA) (op b) =
      precomposeAddHom (hBA.leftActionHom b) := rfl

theorem rightInductionAction_smul (b : B) (φ : NonUnitalModuleHom Aᵐᵒᵖ B M) (b' : B) :
    NonUnitalModule.toEndHom (rightInductionAction hBA) (op b) φ b' = φ (b * b') := rfl

abbrev rightInductionPart (M : Type uM) [AddCommGroup M] [NonUnitalModule Aᵐᵒᵖ M] :=
  homPart hBA hB M

theorem mem_rightInductionPart (φ : NonUnitalModuleHom Aᵐᵒᵖ B M) :
    φ ∈ rightInductionPart hBA hB M ↔
      ∃ e : Idempotent B, ∀ b' : B, φ ((e : B) * b') = φ b' :=
  mem_homPart_iff hBA hB φ

abbrev rightInductionMap (f : NonUnitalModuleHom Aᵐᵒᵖ M N) :
    NonUnitalModuleHom Bᵐᵒᵖ (rightInductionPart hBA hB M) (rightInductionPart hBA hB N) :=
  partMap hBA hB f

theorem rightInductionMap_eq (f : NonUnitalModuleHom Aᵐᵒᵖ M N) :
    rightInductionMap hBA hB f = (ambientMap hBA f).restrictNondegeneratePart hB.op := rfl

theorem rightInductionMap_toAddMonoidHom (f : NonUnitalModuleHom Aᵐᵒᵖ M N) :
    (rightInductionMap hBA hB f).toAddMonoidHom =
      ((ambientMap hBA f).restrictNondegeneratePart hB.op).toAddMonoidHom := rfl

theorem rightInductionMap_val (f : NonUnitalModuleHom Aᵐᵒᵖ M N) (φ : rightInductionPart hBA hB M) :
    (rightInductionMap hBA hB f φ).val = f.comp φ.val := rfl

theorem rightInductionMap_apply (f : NonUnitalModuleHom Aᵐᵒᵖ M N)
    (φ : rightInductionPart hBA hB M) (b : B) :
    (show NonUnitalModuleHom Aᵐᵒᵖ B N from (rightInductionMap hBA hB f φ).val) b =
      f ((show NonUnitalModuleHom Aᵐᵒᵖ B M from φ.val) b) := rfl

/-- Renard's right-module induction, taking the actual `B.op`-nondegenerate Hom part. -/
def rightI : NondegenerateModuleCat.{uA, uM} Aᵐᵒᵖ ⥤
    NondegenerateModuleCat.{uB, max uB uM} Bᵐᵒᵖ :=
  restrictedFunctor hBA hB

theorem rightI_eq : rightI.{uA, uB, uM} hBA hB = restrictedFunctor hBA hB := rfl

theorem rightI_eq_composite : rightI.{uA, uB, uM} hBA hB =
    nondegenerateInclusion Aᵐᵒᵖ ⋙ (ambientFunctor hBA ⋙ nondegeneratePartFunctor hB.op) := rfl

instance rightI_additive : (rightI.{uA, uB, uM} hBA hB).Additive :=
  inferInstanceAs (restrictedFunctor hBA hB).Additive

theorem rightI_obj (M : NondegenerateModuleCat.{uA, uM} Aᵐᵒᵖ) :
    (rightI hBA hB).obj M =
      ⟨NonUnitalModuleCat.of Bᵐᵒᵖ (rightInductionPart hBA hB M.obj),
        nondegeneratePart_isNondegenerate hB.op⟩ := rfl

theorem rightI_obj_carrier (M : NondegenerateModuleCat.{uA, uM} Aᵐᵒᵖ) :
    ((rightI hBA hB).obj M).obj.carrier = rightInductionPart hBA hB M.obj := rfl

theorem rightI_obj_group (M : NondegenerateModuleCat.{uA, uM} Aᵐᵒᵖ) :
    ((rightI hBA hB).obj M).obj.isAddCommGroup =
      (inferInstanceAs (AddCommGroup (rightInductionPart hBA hB M.obj).toAddSubgroup)) := rfl

theorem rightI_obj_action (M : NondegenerateModuleCat.{uA, uM} Aᵐᵒᵖ) :
    ((rightI hBA hB).obj M).obj.isModule =
      (rightInductionPart hBA hB M.obj).instNonUnitalModuleSubtypeMem := rfl

theorem rightI_obj_smul_val (M : NondegenerateModuleCat.{uA, uM} Aᵐᵒᵖ)
    (b : B) (φ : ((rightI hBA hB).obj M).obj) :
    (op b • φ).val = NonUnitalModule.toEndHom (rightInductionAction hBA) (op b) φ.val := rfl

theorem rightI_obj_smul_apply (M : NondegenerateModuleCat.{uA, uM} Aᵐᵒᵖ)
    (b : B) (φ : ((rightI hBA hB).obj M).obj) (b' : B) :
    (show NonUnitalModuleHom Aᵐᵒᵖ B M.obj from (op b • φ).val) b' =
      (show NonUnitalModuleHom Aᵐᵒᵖ B M.obj from φ.val) (b * b') := rfl

theorem rightI_map {M N : NondegenerateModuleCat.{uA, uM} Aᵐᵒᵖ} (f : M ⟶ N) :
    ((rightI hBA hB).map f).hom = (ambientMap hBA f.hom).restrictNondegeneratePart hB.op := rfl

theorem rightI_map_toAddMonoidHom {M N : NondegenerateModuleCat.{uA, uM} Aᵐᵒᵖ} (f : M ⟶ N) :
    ((rightI hBA hB).map f).hom.toAddMonoidHom =
      ((ambientMap hBA f.hom).restrictNondegeneratePart hB.op).toAddMonoidHom := rfl

theorem rightI_map_val {M N : NondegenerateModuleCat.{uA, uM} Aᵐᵒᵖ} (f : M ⟶ N)
    (φ : ((rightI hBA hB).obj M).obj) :
    ((show NonUnitalModuleHom Bᵐᵒᵖ (rightInductionPart hBA hB M.obj) (rightInductionPart hBA hB N.obj) from
      ((rightI hBA hB).map f).hom) φ).val = f.hom.comp φ.val := rfl

theorem rightI_map_apply {M N : NondegenerateModuleCat.{uA, uM} Aᵐᵒᵖ} (f : M ⟶ N)
    (φ : ((rightI hBA hB).obj M).obj) (b' : B) :
    (show NonUnitalModuleHom Aᵐᵒᵖ B N.obj from
      ((show NonUnitalModuleHom Bᵐᵒᵖ (rightInductionPart hBA hB M.obj) (rightInductionPart hBA hB N.obj) from
        ((rightI hBA hB).map f).hom) φ).val) b' =
      (show NonUnitalModuleHom Aᵐᵒᵖ M.obj N.obj from f.hom)
        ((show NonUnitalModuleHom Aᵐᵒᵖ B M.obj from φ.val) b') := rfl

def rightInductionInclusion : rightI.{uA, uB, uM} hBA hB ⋙ nondegenerateInclusion Bᵐᵒᵖ ⟶
    nondegenerateInclusion Aᵐᵒᵖ ⋙ ambientFunctor hBA :=
  restrictedInclusion hBA hB

theorem rightInductionInclusion_eq : rightInductionInclusion.{uA, uB, uM} hBA hB =
    restrictedInclusion hBA hB := rfl

theorem rightInductionInclusion_app (M : NondegenerateModuleCat.{uA, uM} Aᵐᵒᵖ) :
    (rightInductionInclusion hBA hB).app M = (rightInductionPart hBA hB M.obj).subtype := rfl

theorem rightInductionInclusion_app_toAddMonoidHom (M : NondegenerateModuleCat.{uA, uM} Aᵐᵒᵖ) :
    ((rightInductionInclusion hBA hB).app M).toAddMonoidHom =
      (rightInductionPart hBA hB M.obj).toAddSubgroup.subtype := rfl

theorem rightInductionInclusion_app_apply (M : NondegenerateModuleCat.{uA, uM} Aᵐᵒᵖ)
    (φ : ((rightI hBA hB).obj M).obj) :
    (show NonUnitalModuleHom Bᵐᵒᵖ (rightInductionPart hBA hB M.obj) (rightSourceHom hBA M.obj) from
      (rightInductionInclusion hBA hB).app M) φ = φ.val := rfl

theorem rightInductionInclusion_naturality {M N : NondegenerateModuleCat.{uA, uM} Aᵐᵒᵖ} (f : M ⟶ N) :
    (ambientMap hBA f.hom).comp (rightInductionPart hBA hB M.obj).subtype =
      (rightInductionPart hBA hB N.obj).subtype.comp (rightInductionMap hBA hB f.hom) :=
  inclusion_naturality hBA hB f.hom

/-- Adapter for the source assumption on the selected left regular and supplied right actions. -/
abbrev rightIOfNondegenerate (_hBim : IsNondegenerateBimodule B A B) :
    NondegenerateModuleCat.{uA, uM} Aᵐᵒᵖ ⥤ NondegenerateModuleCat.{uB, max uB uM} Bᵐᵒᵖ :=
  rightI hBA hB

theorem rightIOfNondegenerate_eq (hBim : IsNondegenerateBimodule B A B) :
    rightIOfNondegenerate.{uA, uB, uM} hBA hB hBim = rightI hBA hB := rfl

end Induction

/-! Complete unapplied interfaces, including both complementary unequal-universe assignments. -/
set_option linter.checkUnivs false

namespace Checks

private abbrev PseudoActionInterface :=
  {A : Type uA} → {B : Type uB} →
  [NonUnitalRing A] → [NonUnitalRing B] →
  [NonUnitalModule A B] →
  letI : NonUnitalModule Bᵐᵒᵖ B := NonUnitalModule.rightRegular B
  (h : ActionsCommute A B B) →
  {M : Type uM} → [AddCommGroup M] → [NonUnitalModule Bᵐᵒᵖ M] →
  NonUnitalModule Aᵐᵒᵖ (NonUnitalModuleHom Bᵐᵒᵖ B M)
example : PseudoActionInterface.{uA, uB, uM} := @rightPseudoAction.{uA, uB, uM}
example : PseudoActionInterface.{0, 1, 0} := @rightPseudoAction.{0, 1, 0}
example : PseudoActionInterface.{1, 0, 1} := @rightPseudoAction.{1, 0, 1}

private abbrev PseudoPartInterface :=
  {A : Type uA} → {B : Type uB} →
  [NonUnitalRing A] → [NonUnitalRing B] →
  [NonUnitalModule A B] →
  letI : NonUnitalModule Bᵐᵒᵖ B := NonUnitalModule.rightRegular B
  (h : ActionsCommute A B B) →
  (hIdem : IsIdempotented A) →
  (M : Type uM) → [AddCommGroup M] → [NonUnitalModule Bᵐᵒᵖ M] →
  NonUnitalSubmodule Aᵐᵒᵖ (rightSourceHom h M)
example : PseudoPartInterface.{uA, uB, uM} := @rightPseudoPart.{uA, uB, uM}
example : PseudoPartInterface.{0, 1, 0} := @rightPseudoPart.{0, 1, 0}
example : PseudoPartInterface.{1, 0, 1} := @rightPseudoPart.{1, 0, 1}

private abbrev PseudoMapInterface :=
  {A : Type uA} → {B : Type uB} →
  [NonUnitalRing A] → [NonUnitalRing B] →
  [NonUnitalModule A B] →
  letI : NonUnitalModule Bᵐᵒᵖ B := NonUnitalModule.rightRegular B
  (h : ActionsCommute A B B) →
  (hIdem : IsIdempotented A) →
  {M : Type uM} → {N : Type uN} → [AddCommGroup M] → [AddCommGroup N] →
  [NonUnitalModule Bᵐᵒᵖ M] → [NonUnitalModule Bᵐᵒᵖ N] →
  NonUnitalModuleHom Bᵐᵒᵖ M N →
  NonUnitalModuleHom Aᵐᵒᵖ (rightPseudoPart h hIdem M) (rightPseudoPart h hIdem N)
example : PseudoMapInterface.{uA, uB, uM, uN} := @rightPseudoMap.{uA, uB, uM, uN}
example : PseudoMapInterface.{0, 1, 0, 1} := @rightPseudoMap.{0, 1, 0, 1}
example : PseudoMapInterface.{1, 0, 1, 0} := @rightPseudoMap.{1, 0, 1, 0}

private abbrev PseudoFunctorInterface :=
  {A : Type uA} → {B : Type uB} →
  [NonUnitalRing A] → [NonUnitalRing B] →
  [NonUnitalModule A B] →
  letI : NonUnitalModule Bᵐᵒᵖ B := NonUnitalModule.rightRegular B
  (h : ActionsCommute A B B) →
  IsIdempotented A →
  NondegenerateModuleCat.{uB, uM} Bᵐᵒᵖ ⥤
    NondegenerateModuleCat.{uA, max uB uM} Aᵐᵒᵖ
example : PseudoFunctorInterface.{uA, uB, uM} := @rightPseudoF.{uA, uB, uM}
example : PseudoFunctorInterface.{0, 1, 0} := @rightPseudoF.{0, 1, 0}
example : PseudoFunctorInterface.{1, 0, 1} := @rightPseudoF.{1, 0, 1}

private abbrev PseudoInclusionInterface :=
  {A : Type uA} → {B : Type uB} →
  [NonUnitalRing A] → [NonUnitalRing B] →
  [NonUnitalModule A B] →
  letI : NonUnitalModule Bᵐᵒᵖ B := NonUnitalModule.rightRegular B
  (h : ActionsCommute A B B) →
  (hIdem : IsIdempotented A) →
  rightPseudoF.{uA, uB, uM} h hIdem ⋙ nondegenerateInclusion Aᵐᵒᵖ ⟶
    nondegenerateInclusion Bᵐᵒᵖ ⋙ ambientFunctor h
example : PseudoInclusionInterface.{uA, uB, uM} := @rightPseudoInclusion.{uA, uB, uM}
example : PseudoInclusionInterface.{0, 1, 0} := @rightPseudoInclusion.{0, 1, 0}
example : PseudoInclusionInterface.{1, 0, 1} := @rightPseudoInclusion.{1, 0, 1}

private abbrev PseudoAdapterInterface :=
  {A : Type uA} → {B : Type uB} →
  [NonUnitalRing A] → [NonUnitalRing B] →
  [NonUnitalModule A B] →
  letI : NonUnitalModule Bᵐᵒᵖ B := NonUnitalModule.rightRegular B
  (h : ActionsCommute A B B) →
  IsIdempotented A →
  IsNondegenerateBimodule A B B →
  NondegenerateModuleCat.{uB, uM} Bᵐᵒᵖ ⥤
    NondegenerateModuleCat.{uA, max uB uM} Aᵐᵒᵖ
example : PseudoAdapterInterface.{uA, uB, uM} := @rightPseudoFOfNondegenerate.{uA, uB, uM}
example : PseudoAdapterInterface.{0, 1, 0} := @rightPseudoFOfNondegenerate.{0, 1, 0}
example : PseudoAdapterInterface.{1, 0, 1} := @rightPseudoFOfNondegenerate.{1, 0, 1}

private abbrev PseudoAdditiveInterface :=
  {A : Type uA} → {B : Type uB} →
  [NonUnitalRing A] → [NonUnitalRing B] →
  [NonUnitalModule A B] →
  letI : NonUnitalModule Bᵐᵒᵖ B := NonUnitalModule.rightRegular B
  (h : ActionsCommute A B B) →
  (hIdem : IsIdempotented A) →
  (rightPseudoF.{uA, uB, uM} h hIdem).Additive
example : PseudoAdditiveInterface.{uA, uB, uM} := @rightPseudoF_additive.{uA, uB, uM}
example : PseudoAdditiveInterface.{0, 1, 0} := @rightPseudoF_additive.{0, 1, 0}
example : PseudoAdditiveInterface.{1, 0, 1} := @rightPseudoF_additive.{1, 0, 1}

private abbrev PseudoCompositeInterface :=
  {A : Type uA} → {B : Type uB} →
  [NonUnitalRing A] → [NonUnitalRing B] →
  [NonUnitalModule A B] →
  letI : NonUnitalModule Bᵐᵒᵖ B := NonUnitalModule.rightRegular B
  (h : ActionsCommute A B B) →
  (hIdem : IsIdempotented A) →
  rightPseudoF.{uA, uB, uM} h hIdem =
    nondegenerateInclusion Bᵐᵒᵖ ⋙ (ambientFunctor h ⋙ nondegeneratePartFunctor hIdem.op)
example : PseudoCompositeInterface.{uA, uB, uM} := @rightPseudoF_eq_composite.{uA, uB, uM}
example : PseudoCompositeInterface.{0, 1, 0} := @rightPseudoF_eq_composite.{0, 1, 0}
example : PseudoCompositeInterface.{1, 0, 1} := @rightPseudoF_eq_composite.{1, 0, 1}

private abbrev InductionActionInterface :=
  {A : Type uA} → {B : Type uB} →
  [NonUnitalRing A] → [NonUnitalRing B] →
  [NonUnitalModule Aᵐᵒᵖ B] →
  letI : NonUnitalModule B B := NonUnitalModule.regular B
  (h : ActionsCommute B A B) →
  {M : Type uM} → [AddCommGroup M] → [NonUnitalModule Aᵐᵒᵖ M] →
  NonUnitalModule Bᵐᵒᵖ (NonUnitalModuleHom Aᵐᵒᵖ B M)
example : InductionActionInterface.{uA, uB, uM} := @rightInductionAction.{uA, uB, uM}
example : InductionActionInterface.{0, 1, 0} := @rightInductionAction.{0, 1, 0}
example : InductionActionInterface.{1, 0, 1} := @rightInductionAction.{1, 0, 1}

private abbrev InductionPartInterface :=
  {A : Type uA} → {B : Type uB} →
  [NonUnitalRing A] → [NonUnitalRing B] →
  [NonUnitalModule Aᵐᵒᵖ B] →
  letI : NonUnitalModule B B := NonUnitalModule.regular B
  (h : ActionsCommute B A B) →
  (hIdem : IsIdempotented B) →
  (M : Type uM) → [AddCommGroup M] → [NonUnitalModule Aᵐᵒᵖ M] →
  NonUnitalSubmodule Bᵐᵒᵖ (rightSourceHom h M)
example : InductionPartInterface.{uA, uB, uM} := @rightInductionPart.{uA, uB, uM}
example : InductionPartInterface.{0, 1, 0} := @rightInductionPart.{0, 1, 0}
example : InductionPartInterface.{1, 0, 1} := @rightInductionPart.{1, 0, 1}

private abbrev InductionMapInterface :=
  {A : Type uA} → {B : Type uB} →
  [NonUnitalRing A] → [NonUnitalRing B] →
  [NonUnitalModule Aᵐᵒᵖ B] →
  letI : NonUnitalModule B B := NonUnitalModule.regular B
  (h : ActionsCommute B A B) →
  (hIdem : IsIdempotented B) →
  {M : Type uM} → {N : Type uN} → [AddCommGroup M] → [AddCommGroup N] →
  [NonUnitalModule Aᵐᵒᵖ M] → [NonUnitalModule Aᵐᵒᵖ N] →
  NonUnitalModuleHom Aᵐᵒᵖ M N →
  NonUnitalModuleHom Bᵐᵒᵖ (rightInductionPart h hIdem M) (rightInductionPart h hIdem N)
example : InductionMapInterface.{uA, uB, uM, uN} := @rightInductionMap.{uA, uB, uM, uN}
example : InductionMapInterface.{0, 1, 0, 1} := @rightInductionMap.{0, 1, 0, 1}
example : InductionMapInterface.{1, 0, 1, 0} := @rightInductionMap.{1, 0, 1, 0}

private abbrev InductionFunctorInterface :=
  {A : Type uA} → {B : Type uB} →
  [NonUnitalRing A] → [NonUnitalRing B] →
  [NonUnitalModule Aᵐᵒᵖ B] →
  letI : NonUnitalModule B B := NonUnitalModule.regular B
  (h : ActionsCommute B A B) →
  IsIdempotented B →
  NondegenerateModuleCat.{uA, uM} Aᵐᵒᵖ ⥤
    NondegenerateModuleCat.{uB, max uB uM} Bᵐᵒᵖ
example : InductionFunctorInterface.{uA, uB, uM} := @rightI.{uA, uB, uM}
example : InductionFunctorInterface.{0, 1, 0} := @rightI.{0, 1, 0}
example : InductionFunctorInterface.{1, 0, 1} := @rightI.{1, 0, 1}

private abbrev InductionInclusionInterface :=
  {A : Type uA} → {B : Type uB} →
  [NonUnitalRing A] → [NonUnitalRing B] →
  [NonUnitalModule Aᵐᵒᵖ B] →
  letI : NonUnitalModule B B := NonUnitalModule.regular B
  (h : ActionsCommute B A B) →
  (hIdem : IsIdempotented B) →
  rightI.{uA, uB, uM} h hIdem ⋙ nondegenerateInclusion Bᵐᵒᵖ ⟶
    nondegenerateInclusion Aᵐᵒᵖ ⋙ ambientFunctor h
example : InductionInclusionInterface.{uA, uB, uM} := @rightInductionInclusion.{uA, uB, uM}
example : InductionInclusionInterface.{0, 1, 0} := @rightInductionInclusion.{0, 1, 0}
example : InductionInclusionInterface.{1, 0, 1} := @rightInductionInclusion.{1, 0, 1}

private abbrev InductionAdapterInterface :=
  {A : Type uA} → {B : Type uB} →
  [NonUnitalRing A] → [NonUnitalRing B] →
  [NonUnitalModule Aᵐᵒᵖ B] →
  letI : NonUnitalModule B B := NonUnitalModule.regular B
  (h : ActionsCommute B A B) →
  IsIdempotented B →
  IsNondegenerateBimodule B A B →
  NondegenerateModuleCat.{uA, uM} Aᵐᵒᵖ ⥤
    NondegenerateModuleCat.{uB, max uB uM} Bᵐᵒᵖ
example : InductionAdapterInterface.{uA, uB, uM} := @rightIOfNondegenerate.{uA, uB, uM}
example : InductionAdapterInterface.{0, 1, 0} := @rightIOfNondegenerate.{0, 1, 0}
example : InductionAdapterInterface.{1, 0, 1} := @rightIOfNondegenerate.{1, 0, 1}

private abbrev InductionAdditiveInterface :=
  {A : Type uA} → {B : Type uB} →
  [NonUnitalRing A] → [NonUnitalRing B] →
  [NonUnitalModule Aᵐᵒᵖ B] →
  letI : NonUnitalModule B B := NonUnitalModule.regular B
  (h : ActionsCommute B A B) →
  (hIdem : IsIdempotented B) →
  (rightI.{uA, uB, uM} h hIdem).Additive
example : InductionAdditiveInterface.{uA, uB, uM} := @rightI_additive.{uA, uB, uM}
example : InductionAdditiveInterface.{0, 1, 0} := @rightI_additive.{0, 1, 0}
example : InductionAdditiveInterface.{1, 0, 1} := @rightI_additive.{1, 0, 1}

private abbrev InductionCompositeInterface :=
  {A : Type uA} → {B : Type uB} →
  [NonUnitalRing A] → [NonUnitalRing B] →
  [NonUnitalModule Aᵐᵒᵖ B] →
  letI : NonUnitalModule B B := NonUnitalModule.regular B
  (h : ActionsCommute B A B) →
  (hIdem : IsIdempotented B) →
  rightI.{uA, uB, uM} h hIdem =
    nondegenerateInclusion Aᵐᵒᵖ ⋙ (ambientFunctor h ⋙ nondegeneratePartFunctor hIdem.op)
example : InductionCompositeInterface.{uA, uB, uM} := @rightI_eq_composite.{uA, uB, uM}
example : InductionCompositeInterface.{0, 1, 0} := @rightI_eq_composite.{0, 1, 0}
example : InductionCompositeInterface.{1, 0, 1} := @rightI_eq_composite.{1, 0, 1}

/-! Coinciding ring, fixed-source and variable carriers with explicitly competing structures. -/

private abbrev ringGroup (A : Type uA) (r : NonUnitalRing A) : AddCommGroup A :=
  @NonUnitalNonAssocRing.toAddCommGroup A (@NonUnitalRing.toNonUnitalNonAssocRing A r)

section Competing

variable {A : Type uA} [r₁ : NonUnitalRing A] [r₂ : NonUnitalRing A]
  [g₁ : AddCommGroup A] [g₂ : AddCommGroup A]
  (left : @NonUnitalModule A A r₁ (ringGroup A r₁))
  (right : @NonUnitalModule Aᵐᵒᵖ A (@MulOpposite.instNonUnitalRing A r₁) (ringGroup A r₁))
  (target : @NonUnitalModule Aᵐᵒᵖ A (@MulOpposite.instNonUnitalRing A r₁) g₁)
  [otherLeft : @NonUnitalModule A A r₁ (ringGroup A r₁)]
  [otherRight : @NonUnitalModule Aᵐᵒᵖ A (@MulOpposite.instNonUnitalRing A r₁) (ringGroup A r₁)]
  [otherTarget : @NonUnitalModule Aᵐᵒᵖ A (@MulOpposite.instNonUnitalRing A r₁) g₁]
  (hLeft : @ActionsCommute A A A r₁ r₁ (ringGroup A r₁)
    left (@NonUnitalModule.rightRegular A r₁))
  (hRight : @ActionsCommute A A A r₁ r₁ (ringGroup A r₁)
    (@NonUnitalModule.regular A r₁) right)

variable [otherPseudoHom : @NonUnitalModule Aᵐᵒᵖ
  (@NonUnitalModuleHom Aᵐᵒᵖ A A (@MulOpposite.instNonUnitalRing A r₁) (ringGroup A r₁) g₁ (@NonUnitalModule.rightRegular A r₁) target) (@MulOpposite.instNonUnitalRing A r₁)
  (@NonUnitalModuleHom.instAddCommGroup Aᵐᵒᵖ A A (@MulOpposite.instNonUnitalRing A r₁) (ringGroup A r₁) g₁ (@NonUnitalModule.rightRegular A r₁) target)]

set_option linter.overlappingInstances false in
example (hA : @IsIdempotented A r₁) :
    @rightPseudoF.{uA, uA, uM} A A r₁ r₁ left hLeft hA =
      @restrictedFunctor A A A r₁ r₁ (ringGroup A r₁) left (@NonUnitalModule.rightRegular A r₁) hLeft hA := rfl

set_option linter.overlappingInstances false in
example :
    @rightPseudoAction A A r₁ r₁ left hLeft A g₁ target =
      @rightSourceAction A A A A r₁ r₁ (ringGroup A r₁) g₁ left (@NonUnitalModule.rightRegular A r₁) target hLeft := rfl

set_option linter.overlappingInstances false in
example (hA : @IsIdempotented A r₁)
    (hTarget : @IsNondegenerate Aᵐᵒᵖ A (@MulOpposite.instNonUnitalRing A r₁) g₁ target) :
    let X := @NonUnitalModuleCat.of Aᵐᵒᵖ (@MulOpposite.instNonUnitalRing A r₁) A g₁ target
    let N : @NondegenerateModuleCat Aᵐᵒᵖ (@MulOpposite.instNonUnitalRing A r₁) := ⟨X, hTarget⟩
    let F := @rightPseudoF.{uA, uA, uA} A A r₁ r₁ left hLeft hA
    let H := @NonUnitalModuleHom Aᵐᵒᵖ A A (@MulOpposite.instNonUnitalRing A r₁) (ringGroup A r₁) g₁ (@NonUnitalModule.rightRegular A r₁) target
    let G := @NonUnitalModuleHom.instAddCommGroup Aᵐᵒᵖ A A (@MulOpposite.instNonUnitalRing A r₁) (ringGroup A r₁) g₁ (@NonUnitalModule.rightRegular A r₁) target
    let act := @rightSourceAction A A A A r₁ r₁ (ringGroup A r₁) g₁ left (@NonUnitalModule.rightRegular A r₁) target hLeft
    let P := @nondegeneratePart Aᵐᵒᵖ (@MulOpposite.instNonUnitalRing A r₁) (@IsIdempotented.op A r₁ hA) H G act
    @NonUnitalModuleCat.carrier Aᵐᵒᵖ (@MulOpposite.instNonUnitalRing A r₁) (F.obj N).obj = P ∧
    @NonUnitalModuleCat.isAddCommGroup Aᵐᵒᵖ (@MulOpposite.instNonUnitalRing A r₁) (F.obj N).obj =
      (@NonUnitalSubmodule.toAddSubgroup Aᵐᵒᵖ H (@MulOpposite.instNonUnitalRing A r₁) G act P).toAddCommGroup ∧
    @NonUnitalModuleCat.isModule Aᵐᵒᵖ (@MulOpposite.instNonUnitalRing A r₁) (F.obj N).obj =
      @NonUnitalSubmodule.instNonUnitalModuleSubtypeMem Aᵐᵒᵖ H (@MulOpposite.instNonUnitalRing A r₁) G act P :=
  ⟨rfl, rfl, rfl⟩

variable [otherInductionHom : @NonUnitalModule Aᵐᵒᵖ
  (@NonUnitalModuleHom Aᵐᵒᵖ A A (@MulOpposite.instNonUnitalRing A r₁) (ringGroup A r₁) g₁ right target) (@MulOpposite.instNonUnitalRing A r₁)
  (@NonUnitalModuleHom.instAddCommGroup Aᵐᵒᵖ A A (@MulOpposite.instNonUnitalRing A r₁) (ringGroup A r₁) g₁ right target)]

set_option linter.overlappingInstances false in
example (hA : @IsIdempotented A r₁) :
    @rightI.{uA, uA, uM} A A r₁ r₁ right hRight hA =
      @restrictedFunctor A A A r₁ r₁ (ringGroup A r₁) (@NonUnitalModule.regular A r₁) right hRight hA := rfl

set_option linter.overlappingInstances false in
example :
    @rightInductionAction A A r₁ r₁ right hRight A g₁ target =
      @rightSourceAction A A A A r₁ r₁ (ringGroup A r₁) g₁ (@NonUnitalModule.regular A r₁) right target hRight := rfl

set_option linter.overlappingInstances false in
example (hA : @IsIdempotented A r₁)
    (hTarget : @IsNondegenerate Aᵐᵒᵖ A (@MulOpposite.instNonUnitalRing A r₁) g₁ target) :
    let X := @NonUnitalModuleCat.of Aᵐᵒᵖ (@MulOpposite.instNonUnitalRing A r₁) A g₁ target
    let N : @NondegenerateModuleCat Aᵐᵒᵖ (@MulOpposite.instNonUnitalRing A r₁) := ⟨X, hTarget⟩
    let F := @rightI.{uA, uA, uA} A A r₁ r₁ right hRight hA
    let H := @NonUnitalModuleHom Aᵐᵒᵖ A A (@MulOpposite.instNonUnitalRing A r₁) (ringGroup A r₁) g₁ right target
    let G := @NonUnitalModuleHom.instAddCommGroup Aᵐᵒᵖ A A (@MulOpposite.instNonUnitalRing A r₁) (ringGroup A r₁) g₁ right target
    let act := @rightSourceAction A A A A r₁ r₁ (ringGroup A r₁) g₁ (@NonUnitalModule.regular A r₁) right target hRight
    let P := @nondegeneratePart Aᵐᵒᵖ (@MulOpposite.instNonUnitalRing A r₁) (@IsIdempotented.op A r₁ hA) H G act
    @NonUnitalModuleCat.carrier Aᵐᵒᵖ (@MulOpposite.instNonUnitalRing A r₁) (F.obj N).obj = P ∧
    @NonUnitalModuleCat.isAddCommGroup Aᵐᵒᵖ (@MulOpposite.instNonUnitalRing A r₁) (F.obj N).obj =
      (@NonUnitalSubmodule.toAddSubgroup Aᵐᵒᵖ H (@MulOpposite.instNonUnitalRing A r₁) G act P).toAddCommGroup ∧
    @NonUnitalModuleCat.isModule Aᵐᵒᵖ (@MulOpposite.instNonUnitalRing A r₁) (F.obj N).obj =
      @NonUnitalSubmodule.instNonUnitalModuleSubtypeMem Aᵐᵒᵖ H (@MulOpposite.instNonUnitalRing A r₁) G act P :=
  ⟨rfl, rfl, rfl⟩

end Competing

section SubsingletonPseudo

variable {A : Type uA} {B : Type uB} [NonUnitalRing A] [NonUnitalRing B]
  [NonUnitalModule A B]
local instance : NonUnitalModule Bᵐᵒᵖ B := NonUnitalModule.rightRegular B
variable (h : ActionsCommute A B B) (hA : IsIdempotented A)
  (M : Type uM) [AddCommGroup M] [NonUnitalModule Bᵐᵒᵖ M]

example [Subsingleton M] : Subsingleton (rightPseudoPart h hA M) := by
  have : Subsingleton (rightSourceHom h M) := hom_subsingleton
  infer_instance

example [Subsingleton B] : Subsingleton (rightPseudoPart h hA M) := by
  have : Subsingleton (rightSourceHom h M) := hom_subsingleton_of_source
  infer_instance

end SubsingletonPseudo

section SubsingletonInduction

variable {A : Type uA} {B : Type uB} [NonUnitalRing A] [NonUnitalRing B]
  [NonUnitalModule Aᵐᵒᵖ B]
local instance : NonUnitalModule B B := NonUnitalModule.regular B
variable (h : ActionsCommute B A B) (hB : IsIdempotented B)
  (M : Type uM) [AddCommGroup M] [NonUnitalModule Aᵐᵒᵖ M]

example [Subsingleton M] : Subsingleton (rightInductionPart h hB M) := by
  have : Subsingleton (rightSourceHom h M) := hom_subsingleton
  infer_instance

example [Subsingleton B] : Subsingleton (rightInductionPart h hB M) := by
  have : Subsingleton (rightSourceHom h M) := hom_subsingleton_of_source
  infer_instance

end SubsingletonInduction

section IntegerRegular

local instance : NonUnitalModule ℤ ℤ := NonUnitalModule.regular ℤ
local instance : NonUnitalModule ℤᵐᵒᵖ ℤ := NonUnitalModule.rightRegular ℤ

private theorem regularCommute : ActionsCommute ℤ ℤ ℤ :=
  NonUnitalModule.regular_actionsCommute ℤ

private def regularInteger : NondegenerateModuleCat ℤᵐᵒᵖ :=
  ⟨NonUnitalModuleCat.of ℤᵐᵒᵖ ℤ,
    fun n => ⟨⟨op 1, IsIdempotentElem.one⟩, mul_one n⟩⟩

private def regularIdPart : rightPseudoPart regularCommute (IsIdempotented.of_ring ℤ) ℤ :=
  ⟨NonUnitalModuleHom.id ℤᵐᵒᵖ ℤ,
    (mem_rightPseudoPart regularCommute (IsIdempotented.of_ring ℤ) _).mpr
      ⟨⟨1, IsIdempotentElem.one⟩, fun n => one_mul n⟩⟩

example : regularIdPart ≠ 0 := by
  intro h
  have bad : (1 : ℤ) = 0 :=
    congrArg (fun φ : rightPseudoPart regularCommute (IsIdempotented.of_ring ℤ) ℤ =>
      (show NonUnitalModuleHom ℤᵐᵒᵖ ℤ ℤ from φ.val) 1) h
  exact one_ne_zero bad

example (a b : ℤ) :
    NonUnitalModule.toEndHom (rightPseudoAction regularCommute) (op a)
      (NonUnitalModuleHom.id ℤᵐᵒᵖ ℤ) b = a * b := rfl

example (b b' : ℤ) :
    NonUnitalModule.toEndHom (rightInductionAction regularCommute) (op b)
      (NonUnitalModuleHom.id ℤᵐᵒᵖ ℤ) b' = b * b' := rfl

example (a b : ℤ) :
    (show NonUnitalModuleHom ℤᵐᵒᵖ ℤ regularInteger.obj from
      (op a • (show ((rightPseudoF regularCommute (IsIdempotented.of_ring ℤ)).obj regularInteger).obj from
        regularIdPart)).val) b = a * b := rfl

example (b b' : ℤ) :
    (show NonUnitalModuleHom ℤᵐᵒᵖ ℤ regularInteger.obj from
      (op b • (show ((rightI regularCommute (IsIdempotented.of_ring ℤ)).obj regularInteger).obj from
        regularIdPart)).val) b' = b * b' := rfl

example :
    rightPseudoMap regularCommute (IsIdempotented.of_ring ℤ)
      (NonUnitalModuleHom.id ℤᵐᵒᵖ ℤ) regularIdPart = regularIdPart := rfl

example :
    rightInductionMap regularCommute (IsIdempotented.of_ring ℤ)
      (NonUnitalModuleHom.id ℤᵐᵒᵖ ℤ) regularIdPart = regularIdPart := rfl

example :
    (rightPseudoInclusion regularCommute (IsIdempotented.of_ring ℤ)).app regularInteger =
      (rightPseudoPart regularCommute (IsIdempotented.of_ring ℤ) ℤ).subtype := rfl

example :
    (rightInductionInclusion regularCommute (IsIdempotented.of_ring ℤ)).app regularInteger =
      (rightInductionPart regularCommute (IsIdempotented.of_ring ℤ) ℤ).subtype := rfl

example :
    (show NonUnitalModuleHom ℤᵐᵒᵖ (rightPseudoPart regularCommute (IsIdempotented.of_ring ℤ) ℤ)
      (rightSourceHom regularCommute ℤ) from
        (rightPseudoInclusion regularCommute (IsIdempotented.of_ring ℤ)).app regularInteger)
      regularIdPart = NonUnitalModuleHom.id ℤᵐᵒᵖ ℤ := rfl

example :
    (show NonUnitalModuleHom ℤᵐᵒᵖ (rightInductionPart regularCommute (IsIdempotented.of_ring ℤ) ℤ)
      (rightSourceHom regularCommute ℤ) from
        (rightInductionInclusion regularCommute (IsIdempotented.of_ring ℤ)).app regularInteger)
      regularIdPart = NonUnitalModuleHom.id ℤᵐᵒᵖ ℤ := rfl

end IntegerRegular

end Checks

end Langlands.Algebra.RenardRightHomFunctors
