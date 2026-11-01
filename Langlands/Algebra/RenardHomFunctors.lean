import Langlands.Algebra.NondegenerateHomFunctor

/-!
# Renard's pseudo-forgetful functor and right induction

Direct original-Hom specializations of the actual nondegenerate Hom composite.
The two regular actions are selected explicitly, rather than inferred.
-/

set_option autoImplicit false

open CategoryTheory MulOpposite

namespace Langlands.Algebra.RenardHomFunctors

open NonUnitalBimoduleHomActions NondegenerateHomFunctor

universe uA uB uM uN

section Pseudo

variable {A : Type uA} {B : Type uB} [NonUnitalRing A] [NonUnitalRing B]
  [hRight : NonUnitalModule Aᵐᵒᵖ B]

local instance pseudoSourceLeft : NonUnitalModule B B := NonUnitalModule.regular B

variable (hBA : ActionsCommute B A B) (hA : IsIdempotented A)
  {M : Type uM} {N : Type uN} [AddCommGroup M] [AddCommGroup N]
  [NonUnitalModule B M] [NonUnitalModule B N]

/-- The named original residual action on the actual regular-source Hom. -/
abbrev pseudoAction : NonUnitalModule A (NonUnitalModuleHom B B M) :=
  sourceAction hBA

theorem pseudoAction_toEndHom (a : A) :
    NonUnitalModule.toEndHom (pseudoAction (M := M) hBA) a =
      precomposeAddHom (hBA.rightActionHom (op a)) := rfl

theorem pseudoAction_smul (a : A) (φ : NonUnitalModuleHom B B M) (b : B) :
    NonUnitalModule.toEndHom (pseudoAction hBA) a φ b = φ (op a • b) := rfl

/-- The part is taken for `A`, with the supplied right `A`-action on `B`. -/
abbrev pseudoPart (M : Type uM) [AddCommGroup M] [NonUnitalModule B M] :=
  homPart hBA hA M

theorem mem_pseudoPart (φ : NonUnitalModuleHom B B M) :
    φ ∈ pseudoPart hBA hA M ↔
      ∃ e : Idempotent A, ∀ b : B, φ (op (e : A) • b) = φ b :=
  mem_homPart_iff hBA hA φ

abbrev pseudoMap (f : NonUnitalModuleHom B M N) :
    NonUnitalModuleHom A (pseudoPart hBA hA M) (pseudoPart hBA hA N) :=
  partMap hBA hA f

theorem pseudoMap_eq (f : NonUnitalModuleHom B M N) :
    pseudoMap hBA hA f = (ambientMap hBA f).restrictNondegeneratePart hA := rfl

theorem pseudoMap_val (f : NonUnitalModuleHom B M N) (φ : pseudoPart hBA hA M) :
    (pseudoMap hBA hA f φ).val = f.comp φ.val := rfl

/-- The additive pseudo-forgetful functor of I.2.3, in original additive modules. -/
def pseudoF : NondegenerateModuleCat.{uB, uM} B ⥤
    NondegenerateModuleCat.{uA, max uB uM} A :=
  restrictedFunctor hBA hA

theorem pseudoF_eq : pseudoF.{uA, uB, uM} hBA hA = restrictedFunctor hBA hA := rfl

theorem pseudoF_eq_composite : pseudoF.{uA, uB, uM} hBA hA =
    nondegenerateInclusion B ⋙ (ambientFunctor hBA ⋙ nondegeneratePartFunctor hA) := rfl

instance pseudoF_additive : (pseudoF.{uA, uB, uM} hBA hA).Additive :=
  inferInstanceAs (restrictedFunctor hBA hA).Additive

theorem pseudoF_obj (M : NondegenerateModuleCat.{uB, uM} B) :
    (pseudoF hBA hA).obj M =
      ⟨NonUnitalModuleCat.of A (pseudoPart hBA hA M.obj),
        nondegeneratePart_isNondegenerate hA⟩ := rfl

theorem pseudoF_obj_carrier (M : NondegenerateModuleCat.{uB, uM} B) :
    ((pseudoF hBA hA).obj M).obj.carrier = pseudoPart hBA hA M.obj := rfl

theorem pseudoF_obj_group (M : NondegenerateModuleCat.{uB, uM} B) :
    ((pseudoF hBA hA).obj M).obj.isAddCommGroup =
      (inferInstance : AddCommGroup (pseudoPart hBA hA M.obj)) := rfl

theorem pseudoF_obj_action (M : NondegenerateModuleCat.{uB, uM} B) :
    ((pseudoF hBA hA).obj M).obj.isModule =
      (inferInstance : NonUnitalModule A (pseudoPart hBA hA M.obj)) := rfl

theorem pseudoF_obj_smul_val (M : NondegenerateModuleCat.{uB, uM} B)
    (a : A) (φ : ((pseudoF hBA hA).obj M).obj) :
    (a • φ).val = NonUnitalModule.toEndHom (pseudoAction hBA) a φ.val := rfl

theorem pseudoF_obj_smul_apply (M : NondegenerateModuleCat.{uB, uM} B)
    (a : A) (φ : ((pseudoF hBA hA).obj M).obj) (b : B) :
    (show NonUnitalModuleHom B B M.obj from (a • φ).val) b =
      (show NonUnitalModuleHom B B M.obj from φ.val) (op a • b) := rfl

theorem pseudoF_map {M N : NondegenerateModuleCat.{uB, uM} B} (f : M ⟶ N) :
    ((pseudoF hBA hA).map f).hom = (ambientMap hBA f.hom).restrictNondegeneratePart hA := rfl

theorem pseudoF_map_toAddMonoidHom {M N : NondegenerateModuleCat.{uB, uM} B}
    (f : M ⟶ N) :
    ((pseudoF hBA hA).map f).hom.toAddMonoidHom =
      ((ambientMap hBA f.hom).restrictNondegeneratePart hA).toAddMonoidHom := rfl

theorem pseudoF_map_val {M N : NondegenerateModuleCat.{uB, uM} B} (f : M ⟶ N)
    (φ : ((pseudoF hBA hA).obj M).obj) :
    ((show NonUnitalModuleHom A (pseudoPart hBA hA M.obj) (pseudoPart hBA hA N.obj) from
      ((pseudoF hBA hA).map f).hom) φ).val = f.hom.comp φ.val := rfl

theorem pseudoF_map_apply {M N : NondegenerateModuleCat.{uB, uM} B} (f : M ⟶ N)
    (φ : ((pseudoF hBA hA).obj M).obj) (b : B) :
    (show NonUnitalModuleHom B B N.obj from
      ((show NonUnitalModuleHom A (pseudoPart hBA hA M.obj) (pseudoPart hBA hA N.obj) from
        ((pseudoF hBA hA).map f).hom) φ).val) b =
      (show NonUnitalModuleHom B M.obj N.obj from f.hom)
        ((show NonUnitalModuleHom B B M.obj from φ.val) b) := rfl

def pseudoInclusion : pseudoF.{uA, uB, uM} hBA hA ⋙ nondegenerateInclusion A ⟶
    nondegenerateInclusion B ⋙ ambientFunctor hBA :=
  restrictedInclusion hBA hA

theorem pseudoInclusion_app (M : NondegenerateModuleCat.{uB, uM} B) :
    (pseudoInclusion hBA hA).app M = (pseudoPart hBA hA M.obj).subtype := rfl

theorem pseudoInclusion_app_toAddMonoidHom (M : NondegenerateModuleCat.{uB, uM} B) :
    ((pseudoInclusion hBA hA).app M).toAddMonoidHom =
      (pseudoPart hBA hA M.obj).toAddSubgroup.subtype := rfl

theorem pseudoInclusion_app_apply (M : NondegenerateModuleCat.{uB, uM} B)
    (φ : ((pseudoF hBA hA).obj M).obj) :
    (show NonUnitalModuleHom A (pseudoPart hBA hA M.obj) (sourceHom hBA M.obj) from
      (pseudoInclusion hBA hA).app M) φ = φ.val := rfl

theorem pseudoInclusion_naturality {M N : NondegenerateModuleCat.{uB, uM} B} (f : M ⟶ N) :
    (ambientMap hBA f.hom).comp (pseudoPart hBA hA M.obj).subtype =
      (pseudoPart hBA hA N.obj).subtype.comp (pseudoMap hBA hA f.hom) :=
  inclusion_naturality hBA hA f.hom

/-- Adapter for Renard's two-sided nondegeneracy assumption on the specified bimodule. -/
abbrev pseudoFOfNondegenerate (_hBim : IsNondegenerateBimodule B A B) :
    NondegenerateModuleCat.{uB, uM} B ⥤ NondegenerateModuleCat.{uA, max uB uM} A :=
  pseudoF hBA hA

theorem pseudoFOfNondegenerate_eq (hBim : IsNondegenerateBimodule B A B) :
    pseudoFOfNondegenerate.{uA, uB, uM} hBA hA hBim = pseudoF hBA hA := rfl

end Pseudo

section Induction

variable {A : Type uA} {B : Type uB} [NonUnitalRing A] [NonUnitalRing B]
  [hLeft : NonUnitalModule A B]

local instance inductionSourceRight : NonUnitalModule Bᵐᵒᵖ B :=
  NonUnitalModule.rightRegular B

variable (hAB : ActionsCommute A B B) (hB : IsIdempotented B)
  {M : Type uM} {N : Type uN} [AddCommGroup M] [AddCommGroup N]
  [NonUnitalModule A M] [NonUnitalModule A N]

/-- The named source-precomposition action using the right regular action of `B`. -/
abbrev inductionAction : NonUnitalModule B (NonUnitalModuleHom A B M) :=
  sourceAction hAB

theorem inductionAction_toEndHom (b : B) :
    NonUnitalModule.toEndHom (inductionAction (M := M) hAB) b =
      precomposeAddHom (hAB.rightActionHom (op b)) := rfl

theorem inductionAction_smul (b : B) (φ : NonUnitalModuleHom A B M) (b' : B) :
    NonUnitalModule.toEndHom (inductionAction hAB) b φ b' = φ (b' * b) := rfl

abbrev inductionPart (M : Type uM) [AddCommGroup M] [NonUnitalModule A M] :=
  homPart hAB hB M

theorem mem_inductionPart (φ : NonUnitalModuleHom A B M) :
    φ ∈ inductionPart hAB hB M ↔
      ∃ e : Idempotent B, ∀ b' : B, φ (b' * (e : B)) = φ b' :=
  mem_homPart_iff hAB hB φ

abbrev inductionMap (f : NonUnitalModuleHom A M N) :
    NonUnitalModuleHom B (inductionPart hAB hB M) (inductionPart hAB hB N) :=
  partMap hAB hB f

theorem inductionMap_eq (f : NonUnitalModuleHom A M N) :
    inductionMap hAB hB f = (ambientMap hAB f).restrictNondegeneratePart hB := rfl

theorem inductionMap_val (f : NonUnitalModuleHom A M N) (φ : inductionPart hAB hB M) :
    (inductionMap hAB hB f φ).val = f.comp φ.val := rfl

/-- Renard's additive right induction, taking the `B`-nondegenerate Hom part. -/
def I : NondegenerateModuleCat.{uA, uM} A ⥤
    NondegenerateModuleCat.{uB, max uB uM} B :=
  restrictedFunctor hAB hB

theorem I_eq : I.{uA, uB, uM} hAB hB = restrictedFunctor hAB hB := rfl

theorem I_eq_composite : I.{uA, uB, uM} hAB hB =
    nondegenerateInclusion A ⋙ (ambientFunctor hAB ⋙ nondegeneratePartFunctor hB) := rfl

instance I_additive : (I.{uA, uB, uM} hAB hB).Additive :=
  inferInstanceAs (restrictedFunctor hAB hB).Additive

theorem I_obj (M : NondegenerateModuleCat.{uA, uM} A) :
    (I hAB hB).obj M =
      ⟨NonUnitalModuleCat.of B (inductionPart hAB hB M.obj),
        nondegeneratePart_isNondegenerate hB⟩ := rfl

theorem I_obj_carrier (M : NondegenerateModuleCat.{uA, uM} A) :
    ((I hAB hB).obj M).obj.carrier = inductionPart hAB hB M.obj := rfl

theorem I_obj_group (M : NondegenerateModuleCat.{uA, uM} A) :
    ((I hAB hB).obj M).obj.isAddCommGroup =
      (inferInstance : AddCommGroup (inductionPart hAB hB M.obj)) := rfl

theorem I_obj_action (M : NondegenerateModuleCat.{uA, uM} A) :
    ((I hAB hB).obj M).obj.isModule =
      (inferInstance : NonUnitalModule B (inductionPart hAB hB M.obj)) := rfl

theorem I_obj_smul_val (M : NondegenerateModuleCat.{uA, uM} A)
    (b : B) (φ : ((I hAB hB).obj M).obj) :
    (b • φ).val = NonUnitalModule.toEndHom (inductionAction hAB) b φ.val := rfl

theorem I_obj_smul_apply (M : NondegenerateModuleCat.{uA, uM} A)
    (b : B) (φ : ((I hAB hB).obj M).obj) (b' : B) :
    (show NonUnitalModuleHom A B M.obj from (b • φ).val) b' =
      (show NonUnitalModuleHom A B M.obj from φ.val) (b' * b) := rfl

theorem I_map {M N : NondegenerateModuleCat.{uA, uM} A} (f : M ⟶ N) :
    ((I hAB hB).map f).hom = (ambientMap hAB f.hom).restrictNondegeneratePart hB := rfl

theorem I_map_toAddMonoidHom {M N : NondegenerateModuleCat.{uA, uM} A} (f : M ⟶ N) :
    ((I hAB hB).map f).hom.toAddMonoidHom =
      ((ambientMap hAB f.hom).restrictNondegeneratePart hB).toAddMonoidHom := rfl

theorem I_map_val {M N : NondegenerateModuleCat.{uA, uM} A} (f : M ⟶ N)
    (φ : ((I hAB hB).obj M).obj) :
    ((show NonUnitalModuleHom B (inductionPart hAB hB M.obj) (inductionPart hAB hB N.obj) from
      ((I hAB hB).map f).hom) φ).val = f.hom.comp φ.val := rfl

theorem I_map_apply {M N : NondegenerateModuleCat.{uA, uM} A} (f : M ⟶ N)
    (φ : ((I hAB hB).obj M).obj) (b' : B) :
    (show NonUnitalModuleHom A B N.obj from
      ((show NonUnitalModuleHom B (inductionPart hAB hB M.obj) (inductionPart hAB hB N.obj) from
        ((I hAB hB).map f).hom) φ).val) b' =
      (show NonUnitalModuleHom A M.obj N.obj from f.hom)
        ((show NonUnitalModuleHom A B M.obj from φ.val) b') := rfl

def inductionInclusion : I.{uA, uB, uM} hAB hB ⋙ nondegenerateInclusion B ⟶
    nondegenerateInclusion A ⋙ ambientFunctor hAB :=
  restrictedInclusion hAB hB

theorem inductionInclusion_app (M : NondegenerateModuleCat.{uA, uM} A) :
    (inductionInclusion hAB hB).app M = (inductionPart hAB hB M.obj).subtype := rfl

theorem inductionInclusion_app_toAddMonoidHom (M : NondegenerateModuleCat.{uA, uM} A) :
    ((inductionInclusion hAB hB).app M).toAddMonoidHom =
      (inductionPart hAB hB M.obj).toAddSubgroup.subtype := rfl

theorem inductionInclusion_app_apply (M : NondegenerateModuleCat.{uA, uM} A)
    (φ : ((I hAB hB).obj M).obj) :
    (show NonUnitalModuleHom B (inductionPart hAB hB M.obj) (sourceHom hAB M.obj) from
      (inductionInclusion hAB hB).app M) φ = φ.val := rfl

theorem inductionInclusion_naturality {M N : NondegenerateModuleCat.{uA, uM} A} (f : M ⟶ N) :
    (ambientMap hAB f.hom).comp (inductionPart hAB hB M.obj).subtype =
      (inductionPart hAB hB N.obj).subtype.comp (inductionMap hAB hB f.hom) :=
  inclusion_naturality hAB hB f.hom

/-- Adapter for the source's assumption on exactly the specified left action and right regular action. -/
abbrev IOfNondegenerate (_hBim : IsNondegenerateBimodule A B B) :
    NondegenerateModuleCat.{uA, uM} A ⥤ NondegenerateModuleCat.{uB, max uB uM} B :=
  I hAB hB

theorem IOfNondegenerate_eq (hBim : IsNondegenerateBimodule A B B) :
    IOfNondegenerate.{uA, uB, uM} hAB hB hBim = I hAB hB := rfl

end Induction

end Langlands.Algebra.RenardHomFunctors
