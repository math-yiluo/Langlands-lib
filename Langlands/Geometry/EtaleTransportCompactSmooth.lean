import Langlands.Geometry.EtaleTransportLocalAction
import Langlands.Cohomology.HyperextScalarExtension
import Langlands.Representation.Smooth.Transfer.PullbackProof
import Mathlib.CategoryTheory.ObjectProperty.FiniteLimits

/-! # Smooth sections on compact continuous small-etale lifts -/

noncomputable section

universe u w uR uM

namespace Langlands.Geometry.EtaleTransport

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open EtaleCohomologyAction

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

variable {Y : Scheme.{u}} {G : Type w} [Group G] [TopologicalSpace G]
variable (ρ : G →* (Aut Y)ᵐᵒᵖ)

/-- Genuine lifted actions with compact underlying scheme and jointly continuous operators.
The topology here is the scheme topology. -/
def compactContinuousProperty (H : OpenSubgroup G) :
    ObjectProperty (LocalAction ρ (H : Subgroup G)) :=
  fun U => IsCompact (Set.univ : Set U.object.etale.left) ∧
    Continuous (fun p : H × U.object.etale.left => (aut U.action p.1).hom p.2)

/-- Compact continuous open-subgroup lifts, with all equivariant ordinary etale maps. -/
abbrev CompactLocalAction (H : OpenSubgroup G) :=
  (compactContinuousProperty ρ H).FullSubcategory

namespace CompactLocalAction

variable {ρ} {H K : OpenSubgroup G}

/-- Restriction retains the same compact scheme and restricts the continuous operators. -/
def restrict (hKH : (K : Subgroup G) ≤ H) :
    CompactLocalAction ρ H ⥤ CompactLocalAction ρ K :=
  (compactContinuousProperty ρ K).lift
    ((compactContinuousProperty ρ H).ι ⋙ LocalAction.restrict hKH) (by
      intro U
      refine ⟨U.property.1, ?_⟩
      exact U.property.2.comp
        (((continuous_subtype_val.comp continuous_fst).subtype_mk
          (fun p => hKH p.1.property)).prodMk
          continuous_snd))

variable (ρ H)

/-- A compact base with jointly continuous operators supplies a whole-scheme test. -/
def whole (hc : IsCompact (Set.univ : Set Y))
    (hρ : Continuous (fun p : G × Y => (aut ρ p.1).hom p.2)) :
    CompactLocalAction ρ H :=
  ⟨LocalAction.whole ρ H, hc,
    hρ.comp ((continuous_subtype_val.comp continuous_fst).prodMk continuous_snd)⟩

end CompactLocalAction

namespace CompactSmooth

variable (R : Type uR) [CommRing R]

/-- Smoothness on every actual compact continuous open-subgroup lift. -/
def IsSmoothSheaf (F : ModuleSheaf.{u, w, uR, uM} ρ R) : Prop :=
  ∀ (H : OpenSubgroup G) (U : CompactLocalAction ρ H),
    IsSmooth ((LocalAction.sectionRepresentation R U.obj).obj F).ρ

/-- The property defining the compact-continuous test category. -/
def sheafProperty : ObjectProperty (ModuleSheaf.{u, w, uR, uM} ρ R) :=
  IsSmoothSheaf ρ R

/-- Actual transport sheaves with smooth sections on all compact continuous lifts. -/
abbrev ModuleSheaf := (sheafProperty.{u, w, uR, uM} ρ R).FullSubcategory

/-- Retain the actual transport sheaf and all its natural transformations. -/
abbrev inclusion :
    ModuleSheaf.{u, w, uR, uM} ρ R ⥤ EtaleTransport.ModuleSheaf.{u, w, uR, uM} ρ R :=
  (sheafProperty ρ R).ι

instance sheafProperty_isClosedUnderSubobjects :
    (sheafProperty.{u, w, uR, uM} ρ R).IsClosedUnderSubobjects where
  prop_of_mono f _ hF H U := by
    have : Mono ((LocalAction.sectionRepresentation R U.obj).map f) := inferInstance
    exact isSmooth_of_injective
      ((LocalAction.sectionRepresentation R U.obj).map f).hom
      ((Rep.mono_iff_injective _).1 inferInstance) (hF H U)

/-- In particular, the condition is invariant under actual sheaf isomorphisms. -/
theorem isSmoothSheaf_iff_of_iso
    {F E : EtaleTransport.ModuleSheaf.{u, w, uR, uM} ρ R} (e : F ≅ E) :
    IsSmoothSheaf ρ R F ↔ IsSmoothSheaf ρ R E :=
  (sheafProperty ρ R).prop_iff_of_iso e

/-- A discrete acting group makes every local section action smooth. -/
theorem isSmoothSheaf_of_discreteTopology [DiscreteTopology G]
    (F : EtaleTransport.ModuleSheaf.{u, w, uR, uM} ρ R) :
    IsSmoothSheaf ρ R F := by
  intro H U s
  refine ⟨⟨⊥, isOpen_discrete _⟩, ?_⟩
  change ∀ h : (⊥ : Subgroup H), _
  rintro ⟨h, hh⟩
  have hh' : h = 1 := Subgroup.mem_bot.mp hh
  subst h
  simp

/-- Finite limits stay smooth on every test, by exact forgetting of smooth
representations and finite-limit preservation of actual local evaluation. -/
instance sheafProperty_isClosedUnderFiniteLimits :
    (sheafProperty.{u, w, uR, uM} ρ R).IsClosedUnderFiniteLimits where
  isClosedUnderLimitsOfShape J _ _ :=
    ObjectProperty.IsClosedUnderLimitsOfShape.mk' (by
      rintro _ ⟨F, hF⟩ H U
      let E := (LocalAction.sectionRepresentation R U.obj :
        EtaleTransport.ModuleSheaf.{u, w, uR, uM} ρ R ⥤ Rep.{uM} R H)
      let D := (smoothRepProperty R H).lift (F ⋙ E) (fun j => hF j H U)
      let : PreservesFiniteLimits
          (SmoothRep.toRep : SmoothRep.{uR, w, uM} R H ⥤ Rep.{uM} R H) :=
        Functor.preservesFiniteLimits_of_preservesHomology _
      exact (smoothRepProperty R H).prop_of_iso
        ((isLimitOfPreserves SmoothRep.toRep (limit.isLimit D)).conePointUniqueUpToIso
          (isLimitOfPreserves E (limit.isLimit F))) (limit D).property)

instance moduleSheaf_hasFiniteLimits :
    HasFiniteLimits (ModuleSheaf.{u, w, uR, uM} ρ R) := inferInstance

instance inclusion_preservesFiniteLimits :
    PreservesFiniteLimits
      (inclusion.{u, w, uR, uM} ρ R) := inferInstance

/-- On a compact continuous test, retain all sections with their proved smooth action. -/
def sections (H : OpenSubgroup G) (U : CompactLocalAction ρ H) :
    ModuleSheaf.{u, w, uR, uM} ρ R ⥤ SmoothRep.{uR, w, uM} R H :=
  (smoothRepProperty R H).lift
    (inclusion ρ R ⋙ LocalAction.sectionRepresentation R U.obj)
    (fun F => F.property H U)

/-- Forgetting smoothness recovers the original evaluation representation. -/
def sectionsForgetIso (H : OpenSubgroup G) (U : CompactLocalAction ρ H) :
    sections ρ R H U ⋙ SmoothRep.toRep ≅
      inclusion ρ R ⋙ LocalAction.sectionRepresentation R U.obj :=
  Iso.refl _

instance sections_additive (H : OpenSubgroup G) (U : CompactLocalAction ρ H) :
    (sections ρ R H U : ModuleSheaf.{u, w, uR, uM} ρ R ⥤ _).Additive where
  map_add {F E} f g := by
    apply ObjectProperty.hom_ext
    exact (LocalAction.sectionRepresentation R U.obj).map_add (f := f.hom) (g := g.hom)

instance sections_preservesFiniteLimits (H : OpenSubgroup G)
    (U : CompactLocalAction ρ H) :
    PreservesFiniteLimits
      (sections ρ R H U : ModuleSheaf.{u, w, uR, uM} ρ R ⥤ _) := by
  have : PreservesFiniteLimits
      (LocalAction.sectionRepresentation R U.obj :
        EtaleTransport.ModuleSheaf.{u, w, uR, uM} ρ R ⥤ Rep.{uM} R H) :=
    LocalAction.sectionRepresentation_preservesFiniteLimits R U.obj
  have : PreservesFiniteLimits
      ((sections ρ R H U : ModuleSheaf.{u, w, uR, uM} ρ R ⥤ _) ⋙ SmoothRep.toRep) :=
    preservesFiniteLimits_of_natIso (sectionsForgetIso ρ R H U).symm
  exact preservesFiniteLimits_of_reflects_of_preserves _ SmoothRep.toRep

/-- Equivariant geometric restriction retains the actual sheaf restriction map. -/
def sectionRestriction {H : OpenSubgroup G} {U V : CompactLocalAction ρ H}
    (f : U ⟶ V) :
    sections ρ R H V ⟶ (sections ρ R H U :
      ModuleSheaf.{u, w, uR, uM} ρ R ⥤ _) where
  app F := ObjectProperty.homMk
    ((LocalAction.representationRestriction R f.hom).app F.obj)
  naturality {F E} g := by
    apply ObjectProperty.hom_ext
    exact (LocalAction.representationRestriction R f.hom).naturality g.hom

/-- The complete smooth local-section representations form a contravariant diagram. -/
def sectionDiagram (H : OpenSubgroup G) :
    (CompactLocalAction ρ H)ᵒᵖ ⥤
      (ModuleSheaf.{u, w, uR, uM} ρ R ⥤ SmoothRep.{uR, w, uM} R H) where
  obj U := sections ρ R H U.unop
  map f := sectionRestriction ρ R f.unop
  map_id U := by
    apply NatTrans.ext
    funext F
    apply ObjectProperty.hom_ext
    apply Rep.hom_ext
    apply Representation.IntertwiningMap.ext
    change (F.obj.obj.map
      ((EtaleTransport.inclusion ρ).map (𝟙 U.unop.obj.object.etale)).op).hom = LinearMap.id
    rw [CategoryTheory.Functor.map_id, op_id, CategoryTheory.Functor.map_id]
    rfl
  map_comp f g := by
    apply NatTrans.ext
    funext F
    apply ObjectProperty.hom_ext
    apply Rep.hom_ext
    apply Representation.IntertwiningMap.ext
    change (F.obj.obj.map ((EtaleTransport.inclusion ρ).map
        (g.unop.hom.hom ≫ f.unop.hom.hom)).op).hom = _
    rw [CategoryTheory.Functor.map_comp, op_comp, CategoryTheory.Functor.map_comp]
    rfl

/-- On a compact continuous base, the whole test gives the existing global
representation restricted to the open subgroup. -/
def wholeSectionsForgetIso (H : OpenSubgroup G) (hc : IsCompact (Set.univ : Set Y))
    (hρ : Continuous (fun p : G × Y => (aut ρ p.1).hom p.2)) :
    sections ρ R H (CompactLocalAction.whole ρ H hc hρ) ⋙ SmoothRep.toRep ≅
      inclusion ρ R ⋙
        (EtaleTransport.sectionRepresentation ρ R :
          EtaleTransport.ModuleSheaf.{u, w, uR, uM} ρ R ⥤ Rep.{uM} R G) ⋙
        Rep.resFunctor H.subtype :=
  Functor.isoWhiskerLeft (inclusion ρ R)
    (LocalAction.wholeRepresentationIso (ρ := ρ) (H := (H : Subgroup G)) R)

/-- For a compact continuous base action, the test at the full subgroup proves
smoothness of the complete global section representation. -/
theorem isSmooth_globalSections (hc : IsCompact (Set.univ : Set Y))
    (hρ : Continuous (fun p : G × Y => (aut ρ p.1).hom p.2))
    (F : ModuleSheaf.{u, w, uR, uM} ρ R) :
    IsSmooth ((EtaleTransport.sectionRepresentation ρ R).obj F.obj).ρ := by
  let φ : G →* (⊤ : OpenSubgroup G) :=
    { toFun g := ⟨g, OpenSubgroup.mem_top g⟩
      map_one' := rfl
      map_mul' _ _ := rfl }
  exact isSmooth_comp φ (continuous_id.subtype_mk _)
    (F.property ⊤ (CompactLocalAction.whole ρ ⊤ hc hρ))

/-- Complete global sections of a qualifying sheaf, with their proved smooth action. -/
def globalSections (hc : IsCompact (Set.univ : Set Y))
    (hρ : Continuous (fun p : G × Y => (aut ρ p.1).hom p.2)) :
    ModuleSheaf.{u, w, uR, uM} ρ R ⥤ SmoothRep.{uR, w, uM} R G :=
  (smoothRepProperty R G).lift
    (inclusion ρ R ⋙ EtaleTransport.sectionRepresentation ρ R)
    (isSmooth_globalSections ρ R hc hρ)

/-- Forgetting the proved global smoothness retains the full original representation. -/
def globalSectionsForgetIso (hc : IsCompact (Set.univ : Set Y))
    (hρ : Continuous (fun p : G × Y => (aut ρ p.1).hom p.2)) :
    globalSections ρ R hc hρ ⋙ SmoothRep.toRep ≅
      inclusion ρ R ⋙
        (EtaleTransport.sectionRepresentation ρ R :
          EtaleTransport.ModuleSheaf.{u, w, uR, uM} ρ R ⥤ Rep.{uM} R G) :=
  Iso.refl _

instance globalSections_additive (hc : IsCompact (Set.univ : Set Y))
    (hρ : Continuous (fun p : G × Y => (aut ρ p.1).hom p.2)) :
    (globalSections ρ R hc hρ : ModuleSheaf.{u, w, uR, uM} ρ R ⥤ _).Additive where
  map_add {F E} f g := by
    apply ObjectProperty.hom_ext
    exact (EtaleTransport.sectionRepresentation ρ R).map_add (f := f.hom) (g := g.hom)

instance globalSections_preservesFiniteLimits (hc : IsCompact (Set.univ : Set Y))
    (hρ : Continuous (fun p : G × Y => (aut ρ p.1).hom p.2)) :
    PreservesFiniteLimits
      (globalSections ρ R hc hρ : ModuleSheaf.{u, w, uR, uM} ρ R ⥤ _) := by
  have : PreservesFiniteLimits
      ((globalSections ρ R hc hρ : ModuleSheaf.{u, w, uR, uM} ρ R ⥤ _) ⋙
        SmoothRep.toRep) :=
    preservesFiniteLimits_of_natIso (globalSectionsForgetIso ρ R hc hρ).symm
  exact preservesFiniteLimits_of_reflects_of_preserves _ SmoothRep.toRep

end CompactSmooth

end Langlands.Geometry.EtaleTransport
