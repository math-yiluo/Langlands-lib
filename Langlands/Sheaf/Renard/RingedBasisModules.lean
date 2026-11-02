import Langlands.Sheaf.Renard.BasisSheaf
import Mathlib.Algebra.Category.ModuleCat.Presheaf

/-!
# Actual module sheaves on a ringed basis

The category uses Mathlib's original module presheaves and the intrinsic
Renard basis sheaf condition. The space, ring and module universes are independent.
-/

open CategoryTheory Opposite TopologicalSpace

universe u r v

namespace Langlands.Sheaf.Renard

variable {X : Type u} [TopologicalSpace X] {B : OpenBasis X}

/-- The literal ring-sheaf condition is the condition on the underlying additive presheaf. -/
def RingSheafCondition (S : (BasisOpen B)ᵒᵖ ⥤ RingCat.{r}) : Prop :=
  SheafCondition (S ⋙ forget₂ RingCat AddCommGrpCat)

/-- A genuine ring sheaf on the chosen basis, with its intrinsic sheaf proof. -/
structure RingedBasis (B : OpenBasis X) where
  ring : (BasisOpen B)ᵒᵖ ⥤ RingCat.{r}
  isSheaf : RingSheafCondition ring

/-- The actual ring restriction along an inclusion of basis opens. -/
def ringRestriction (S : (BasisOpen B)ᵒᵖ ⥤ RingCat.{r})
    {U V : BasisOpen B} (h : U.obj ≤ V.obj) : S.obj (op V) ⟶ S.obj (op U) :=
  S.map (basisHom h).op

/-- Actual module presheaves whose original underlying additive presheaf is a sheaf. -/
abbrev BasisModuleSheaf (S : (BasisOpen B)ᵒᵖ ⥤ RingCat.{r}) :=
  (show ObjectProperty (PresheafOfModules.{v} S) from
    fun M => SheafCondition M.presheaf).FullSubcategory

/-- The ringed-basis specialization retains the proof that the ring itself is a sheaf. -/
abbrev RingedBasis.ModuleSheaf (S : RingedBasis.{u,r} B) :=
  BasisModuleSheaf.{u,r,v} S.ring

/-- The inclusion keeps the original module objects and semilinear restrictions. -/
def moduleSheafInclusion (S : (BasisOpen B)ᵒᵖ ⥤ RingCat.{r}) :
    BasisModuleSheaf.{u,r,v} S ⥤ PresheafOfModules.{v} S :=
  ObjectProperty.ι _

instance (S : (BasisOpen B)ᵒᵖ ⥤ RingCat.{r}) :
    (moduleSheafInclusion.{u,r,v} S).Full :=
  inferInstanceAs (ObjectProperty.ι _).Full

instance (S : (BasisOpen B)ᵒᵖ ⥤ RingCat.{r}) :
    (moduleSheafInclusion.{u,r,v} S).Faithful :=
  inferInstanceAs (ObjectProperty.ι _).Faithful

namespace BasisModuleSheaf

variable {S : (BasisOpen B)ᵒᵖ ⥤ RingCat.{r}}

/-- The original module of sections, with no carrier replacement. -/
abbrev sections (M : BasisModuleSheaf.{u,r,v} S) (U : BasisOpen B) :
    ModuleCat.{v} (S.obj (op U)) :=
  M.obj.obj (op U)

/-- The original restriction, bundled as a semilinear map along the ring restriction. -/
noncomputable def restrict (M : BasisModuleSheaf.{u,r,v} S)
    {U V : BasisOpen B} (h : U.obj ≤ V.obj) :
    M.sections V →ₛₗ[(ringRestriction S h).hom] M.sections U :=
  M.obj.restrictₛₗ (basisHom h).op

@[simp]
theorem restrict_apply (M : BasisModuleSheaf.{u,r,v} S)
    {U V : BasisOpen B} (h : U.obj ≤ V.obj) (m : M.sections V) :
    M.restrict h m = M.obj.map (basisHom h).op m := rfl

/-- The restriction-of-scalars law in the source, on the original sections. -/
theorem restrict_smul (M : BasisModuleSheaf.{u,r,v} S)
    {U V : BasisOpen B} (h : U.obj ≤ V.obj)
    (a : S.obj (op V)) (m : M.sections V) :
    M.restrict h (a • m) = ringRestriction S h a • M.restrict h m :=
  M.obj.map_smul (basisHom h).op a m

@[simp]
theorem underlying_sections (M : BasisModuleSheaf.{u,r,v} S) (U : BasisOpen B) :
    (Sections M.obj.presheaf U : Type v) = M.sections U := rfl

@[simp]
theorem underlying_restriction (M : BasisModuleSheaf.{u,r,v} S)
    {U V : BasisOpen B} (h : U.obj ≤ V.obj) (m : M.sections V) :
    restriction M.obj.presheaf h m = M.restrict h m := rfl

/-- Empty normalization is a consequence of the sheaf axiom, never extra object data. -/
theorem isNormalized (M : BasisModuleSheaf.{u,r,v} S) : IsNormalized M.obj.presheaf :=
  SheafCondition.isNormalized _ M.property

theorem empty_section_eq_zero (M : BasisModuleSheaf.{u,r,v} S)
    (U : BasisOpen B) (hU : U.obj = ⊥) (m : M.sections U) : m = 0 :=
  (isNormalized_iff_zero _).mp M.isNormalized U hU m

/-- The actual scalar-linear component of a module-sheaf morphism. -/
abbrev app {M N : BasisModuleSheaf.{u,r,v} S} (f : M ⟶ N) (U : BasisOpen B) :
    M.sections U ⟶ N.sections U :=
  f.hom.app (op U)

theorem app_restrict {M N : BasisModuleSheaf.{u,r,v} S} (f : M ⟶ N)
    {U V : BasisOpen B} (h : U.obj ≤ V.obj) (m : M.sections V) :
    app f U (M.restrict h m) = N.restrict h (app f V m) :=
  PresheafOfModules.naturality_apply f.hom (basisHom h).op m

@[simp]
theorem id_app (M : BasisModuleSheaf.{u,r,v} S) (U : BasisOpen B) :
    app (𝟙 M) U = 𝟙 (M.sections U) := rfl

@[simp]
theorem comp_app {M N P : BasisModuleSheaf.{u,r,v} S}
    (f : M ⟶ N) (g : N ⟶ P) (U : BasisOpen B) :
    app (f ≫ g) U = app f U ≫ app g U := rfl

@[ext]
theorem hom_ext {M N : BasisModuleSheaf.{u,r,v} S} {f g : M ⟶ N}
    (h : ∀ (U : BasisOpen B) (m : M.sections U), app f U m = app g U m) : f = g := by
  apply ObjectProperty.hom_ext
  apply PresheafOfModules.hom_ext
  intro U
  ext m
  exact h U.unop m

/-- Scalar preservation is an explicit condition on an additive natural transformation. -/
def PreservesScalars (M N : BasisModuleSheaf.{u,r,v} S)
    (f : M.obj.presheaf ⟶ N.obj.presheaf) : Prop :=
  ∀ (U : BasisOpen B) (a : S.obj (op U)) (m : M.sections U),
    f.app (op U) (a • m) = a • f.app (op U) m

/-- Additive natural transformations lift exactly when their components preserve scalars. -/
noncomputable def homMk {M N : BasisModuleSheaf.{u,r,v} S}
    (f : M.obj.presheaf ⟶ N.obj.presheaf) (hf : PreservesScalars M N f) : M ⟶ N :=
  ObjectProperty.homMk (PresheafOfModules.homMk f (fun U => hf U.unop))

@[simp]
theorem homMk_app {M N : BasisModuleSheaf.{u,r,v} S}
    (f : M.obj.presheaf ⟶ N.obj.presheaf) (hf : PreservesScalars M N f)
    (U : BasisOpen B) (m : M.sections U) :
    app (homMk f hf) U m = f.app (op U) m := rfl

/-- Morphisms are exactly the scalar-preserving additive natural transformations. -/
noncomputable def homEquiv (M N : BasisModuleSheaf.{u,r,v} S) :
    (M ⟶ N) ≃ {f : M.obj.presheaf ⟶ N.obj.presheaf // PreservesScalars M N f} where
  toFun f := ⟨(PresheafOfModules.toPresheaf S).map f.hom,
    fun U a m => (f.hom.app (op U)).hom.map_smul a m⟩
  invFun f := homMk f.val f.property
  left_inv f := by
    apply hom_ext
    intro U m
    rfl
  right_inv f := by
    apply Subtype.ext
    ext U m
    rfl

end BasisModuleSheaf

/-- Forget the scalar action, deriving normalization from the same sheaf proof. -/
noncomputable def moduleSheafToBasisSheaf (S : (BasisOpen B)ᵒᵖ ⥤ RingCat.{r}) :
    BasisModuleSheaf.{u,r,v} S ⥤ BasisSheaf.{u,v} B where
  obj M := ⟨⟨M.obj.presheaf, M.isNormalized⟩, M.property⟩
  map f := ObjectProperty.homMk
    (ObjectProperty.homMk ((PresheafOfModules.toPresheaf S).map f.hom))
  map_id M := by
    apply ObjectProperty.hom_ext
    apply ObjectProperty.hom_ext
    exact (PresheafOfModules.toPresheaf S).map_id M.obj
  map_comp f g := by
    apply ObjectProperty.hom_ext
    apply ObjectProperty.hom_ext
    exact (PresheafOfModules.toPresheaf S).map_comp f.hom g.hom

instance (S : (BasisOpen B)ᵒᵖ ⥤ RingCat.{r}) :
    (moduleSheafToBasisSheaf.{u,r,v} S).Faithful where
  map_injective {M N f g} h := by
    apply ObjectProperty.hom_ext
    apply (PresheafOfModules.toPresheaf S).map_injective
    exact congrArg (fun k => k.hom.hom) h

/-- Both forgetful routes give the very same underlying additive presheaf functor. -/
theorem moduleSheaf_forget_comparison (S : (BasisOpen B)ᵒᵖ ⥤ RingCat.{r}) :
    moduleSheafToBasisSheaf.{u,r,v} S ⋙ sheafForget B ⋙ presheafInclusion B =
      moduleSheafInclusion S ⋙ PresheafOfModules.toPresheaf S := rfl

/-- Evaluation is evaluation of the original module presheaf. -/
def moduleSheafEvaluation (S : (BasisOpen B)ᵒᵖ ⥤ RingCat.{r}) (U : BasisOpen B) :
    BasisModuleSheaf.{u,r,v} S ⥤ ModuleCat.{v} (S.obj (op U)) :=
  moduleSheafInclusion S ⋙ PresheafOfModules.evaluation S (op U)

@[simp]
theorem moduleSheafToBasisSheaf_sections (S : (BasisOpen B)ᵒᵖ ⥤ RingCat.{r})
    (M : BasisModuleSheaf.{u,r,v} S) (U : BasisOpen B) :
    (Sections ((moduleSheafToBasisSheaf S).obj M).obj.obj U : Type v) =
      M.sections U := rfl

@[simp]
theorem moduleSheafToBasisSheaf_map_app (S : (BasisOpen B)ᵒᵖ ⥤ RingCat.{r})
    {M N : BasisModuleSheaf.{u,r,v} S} (f : M ⟶ N)
    (U : BasisOpen B) (m : M.sections U) :
    ((moduleSheafToBasisSheaf S).map f).hom.hom.app (op U) m =
      BasisModuleSheaf.app f U m := rfl

@[simp]
theorem moduleSheafEvaluation_obj (S : (BasisOpen B)ᵒᵖ ⥤ RingCat.{r})
    (U : BasisOpen B) (M : BasisModuleSheaf.{u,r,v} S) :
    (moduleSheafEvaluation S U).obj M = M.sections U := rfl

@[simp]
theorem moduleSheafEvaluation_map (S : (BasisOpen B)ᵒᵖ ⥤ RingCat.{r})
    (U : BasisOpen B) {M N : BasisModuleSheaf.{u,r,v} S} (f : M ⟶ N) :
    (moduleSheafEvaluation S U).map f = BasisModuleSheaf.app f U := rfl

/-- Forgetting the evaluated scalar action recovers evaluation of the underlying sheaf. -/
theorem moduleSheafEvaluation_forget (S : (BasisOpen B)ᵒᵖ ⥤ RingCat.{r})
    (U : BasisOpen B) :
    moduleSheafEvaluation.{u,r,v} S U ⋙ forget₂ (ModuleCat (S.obj (op U))) AddCommGrpCat =
      moduleSheafToBasisSheaf S ⋙ sheafForget B ⋙ presheafInclusion B ⋙
        (CategoryTheory.evaluation _ _).obj (op U) := rfl

end Langlands.Sheaf.Renard
