import Langlands.Geometry.EtaleTransportSite
import Langlands.Geometry.EtaleDerivedSections
import Mathlib.CategoryTheory.Sites.Limits
import Mathlib.RepresentationTheory.Rep.Basic
import Mathlib.Algebra.Homology.Additive
import Mathlib.Algebra.Homology.Functor

/-! # Actual section representations of small-etale transport sheaves -/

noncomputable section

universe u w uA vA uR uM uJ vJ uI

namespace Langlands.Geometry.EtaleTransport

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open EtaleCohomologyAction

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

variable {Y : Scheme.{u}} {G : Type w} [Group G]
variable (ρ : G →* (Aut Y)ᵐᵒᵖ)

/-- The identity small-etale scheme, viewed in the transport category. -/
def whole : Object ρ := ⟨Scheme.Etale.mk (𝟙 Y)⟩

/-- The ordinary identity small-etale object is terminal. -/
def wholeIsTerminal : IsTerminal (whole ρ).etale :=
  IsTerminal.ofUniqueHom
    (fun U => MorphismProperty.Over.homMk U.hom (by simp [whole]))
    (fun U f => MorphismProperty.Over.Hom.ext (by simpa [whole] using f.w))

/-- The automorphism of the whole scheme with its specified group label. -/
def wholeMap (g : G) : whole ρ ⟶ whole ρ where
  label := g
  left := (aut ρ g).hom
  w := by simp [whole]

@[simp] theorem wholeMap_label (g : G) : (wholeMap ρ g).label = g := rfl
@[simp] theorem wholeMap_left (g : G) : (wholeMap ρ g).left = (aut ρ g).hom := rfl

@[simp] theorem wholeMap_one : wholeMap ρ 1 = 𝟙 (whole ρ) :=
  Object.Hom.ext rfl (by simp [whole, aut_one])

/-- Multiplication follows the scheme automorphism convention of the transport site. -/
theorem wholeMap_mul (g h : G) : wholeMap ρ (g * h) = wholeMap ρ g ≫ wholeMap ρ h :=
  Object.Hom.ext rfl (by simp [aut_mul])

variable (A : Type uA) [Category.{vA} A]

/-- Sections over any genuine small-etale transport object. -/
abbrev evaluation (U : Object ρ) : Sheaf ρ A ⥤ A :=
  (sheafSections (transportTopology ρ) A).obj (op U)

/-- Global sections with the action induced by the actual labelled scheme maps. -/
def sectionAction : Sheaf ρ A ⥤ Action A G where
  obj F :=
    { V := F.obj.obj (op (whole ρ))
      ρ :=
        { toFun g := F.obj.map (wholeMap ρ g).op
          map_one' := by rw [wholeMap_one, op_id, F.obj.map_id]; rfl
          map_mul' g h := by
            rw [wholeMap_mul, op_comp, F.obj.map_comp]
            rfl } }
  map f :=
    { hom := f.hom.app (op (whole ρ))
      comm g := f.hom.naturality (wholeMap ρ g).op }

@[simp]
theorem sectionAction_obj_ρ (F : Sheaf ρ A) (g : G) :
    ((sectionAction ρ A).obj F).ρ g = F.obj.map (wholeMap ρ g).op := rfl

@[simp]
theorem sectionAction_map_hom {F H : Sheaf ρ A} (f : F ⟶ H) :
    ((sectionAction ρ A).map f).hom = f.hom.app (op (whole ρ)) := rfl

/-- The action has exactly the module of ordinary whole-scheme sections underneath. -/
def sectionActionForgetIso :
    sectionAction ρ A ⋙ Action.forget A G ≅ evaluation ρ A (whole ρ) :=
  Iso.refl _

/-- Ordinary restriction and transport evaluation have identical sections. -/
def evaluationToSheafIso (U : Object ρ) :
    evaluation ρ A U ≅ toSheaf ρ A ⋙
      (sheafSections Y.smallEtaleTopology A).obj (op U.etale) :=
  Iso.refl _

section Limits

variable (J : Type uJ) [Category.{vJ} J] [HasLimitsOfShape J A]

instance evaluation_preservesLimitsOfShape (U : Object ρ) :
    PreservesLimitsOfShape J (evaluation ρ A U) :=
  inferInstanceAs (PreservesLimitsOfShape J
    (sheafToPresheaf (transportTopology ρ) A ⋙ (CategoryTheory.evaluation _ _).obj (op U)))

instance toSheaf_preservesLimitsOfShape :
    PreservesLimitsOfShape J (toSheaf ρ A) := by
  have : PreservesLimitsOfShape J
      (toSheaf ρ A ⋙ sheafToPresheaf Y.smallEtaleTopology A) :=
    inferInstanceAs (PreservesLimitsOfShape J
      (sheafToPresheaf (transportTopology ρ) A ⋙
        (Functor.whiskeringLeft _ _ A).obj (inclusion ρ).op))
  exact preservesLimitsOfShape_of_reflects_of_preserves (toSheaf ρ A)
    (sheafToPresheaf Y.smallEtaleTopology A)

end Limits

instance evaluation_preservesFiniteLimits [HasFiniteLimits A] (U : Object ρ) :
    PreservesFiniteLimits (evaluation ρ A U) := ⟨fun _ _ _ => inferInstance⟩

instance toSheaf_preservesFiniteLimits [HasFiniteLimits A] :
    PreservesFiniteLimits (toSheaf ρ A) := ⟨fun _ _ _ => inferInstance⟩

section Modules

variable (R : Type uR) [CommRing R]

/-- Actual module sheaves on the scheme transport site. -/
abbrev ModuleSheaf := Sheaf ρ (ModuleCat.{uM} R)

/-- Global sections as algebraic representations of the acting group. -/
def sectionRepresentation : ModuleSheaf.{u, w, uR, uM} ρ R ⥤ Rep.{uM} R G :=
  sectionAction ρ (ModuleCat.{uM} R) ⋙ Rep.ActionToRep R G

instance sectionRepresentation_additive :
    (sectionRepresentation ρ R : ModuleSheaf.{u, w, uR, uM} ρ R ⥤ Rep.{uM} R G).Additive where
  map_add {F H} f g := by ext s; rfl

/-- Forgetting the representation recovers ordinary whole-scheme evaluation. -/
def sectionRepresentationForgetIso :
    sectionRepresentation ρ R ⋙ forget₂ (Rep.{uM} R G) (ModuleCat.{uM} R) ≅
      evaluation ρ (ModuleCat.{uM} R) (whole ρ) :=
  Iso.refl _

instance sectionRepresentation_preservesFiniteLimits :
    PreservesFiniteLimits
      (sectionRepresentation ρ R : ModuleSheaf.{u, w, uR, uM} ρ R ⥤ Rep.{uM} R G) := by
  have : PreservesFiniteLimits
      (sectionRepresentation ρ R ⋙ forget₂ (Rep.{uM} R G) (ModuleCat.{uM} R)) :=
    preservesFiniteLimits_of_natIso (sectionRepresentationForgetIso ρ R).symm
  exact preservesFiniteLimits_of_reflects_of_preserves _
    (forget₂ (Rep.{uM} R G) (ModuleCat.{uM} R))

variable {I : Type uI} (c : ComplexShape I)

/-- Every strict complex of transport sheaves gives a strict representation complex. -/
def sectionComplex :
    HomologicalComplex (ModuleSheaf.{u, w, uR, uM} ρ R) c ⥤
      HomologicalComplex (Rep.{uM} R G) c :=
  (sectionRepresentation ρ R).mapHomologicalComplex c

/-- The underlying complex is the actual whole-scheme section complex. -/
def sectionComplexForgetIso :
    sectionComplex ρ R c ⋙ (forget₂ (Rep.{uM} R G) (ModuleCat.{uM} R)).mapHomologicalComplex c ≅
      (evaluation ρ (ModuleCat.{uM} R) (whole ρ)).mapHomologicalComplex c :=
  Functor.mapHomologicalComplexCompIso (sectionRepresentationForgetIso ρ R) c

end Modules

/-- In the ordinary small-etale module universe, forgotten section representations
are the existing global-section functor of the underlying actual etale sheaf. -/
def sectionRepresentationOrdinaryIso (R : Type u) [CommRing R] :
    sectionRepresentation ρ R ⋙ forget₂ (Rep.{u} R G) (ModuleCat.{u} R) ≅
      toSheaf ρ (ModuleCat.{u} R) ⋙ EtaleDerivedSections.sections Y R :=
  sectionRepresentationForgetIso ρ R ≪≫
    evaluationToSheafIso ρ (ModuleCat.{u} R) (whole ρ) ≪≫
    Functor.isoWhiskerLeft (toSheaf ρ (ModuleCat.{u} R))
      (CategoryTheory.Sheaf.ΓNatIsoSheafSections Y.smallEtaleTopology
        (ModuleCat.{u} R) (wholeIsTerminal ρ)).symm

end Langlands.Geometry.EtaleTransport
