import Langlands.Sheaf.Renard.BasisPresheaf
import Mathlib.CategoryTheory.Filtered.Basic
import Mathlib.CategoryTheory.Whiskering
import Mathlib.Algebra.Category.Grp.Colimits

/-!
# Stalks of Renard's presheaves on a chosen basis

The neighborhood category has reverse-inclusion arrows. Values are lifted
from universe `v` to `max u v` before taking the abelian-group colimit.
-/

open CategoryTheory CategoryTheory.Functor CategoryTheory.Limits Opposite TopologicalSpace

universe u v

namespace Langlands.Sheaf.Renard

variable {X : Type u} [TopologicalSpace X]

/-- The actual basis neighborhoods of a point, with reverse-inclusion arrows. -/
abbrev BasisNeighborhood (B : OpenBasis X) (x : X) :=
  (show ObjectProperty ((BasisOpen B)ᵒᵖ) from fun U => x ∈ U.unop.obj).FullSubcategory

/-- Inclusion into the opposite basis category, retaining the restriction direction. -/
def neighborhoodInclusion (B : OpenBasis X) (x : X) :
    BasisNeighborhood B x ⥤ (BasisOpen B)ᵒᵖ :=
  ObjectProperty.ι _

/-- The arrow from a larger neighborhood to a smaller one. -/
def neighborhoodHom {B : OpenBasis X} {x : X} {U V : BasisNeighborhood B x}
    (h : V.obj.unop.obj ≤ U.obj.unop.obj) : U ⟶ V :=
  ObjectProperty.homMk (basisHom h).op

theorem neighborhood_hom_nonempty_iff {B : OpenBasis X} {x : X}
    (U V : BasisNeighborhood B x) :
    Nonempty (U ⟶ V) ↔ V.obj.unop.obj ≤ U.obj.unop.obj :=
  ⟨fun ⟨f⟩ => f.hom.unop.hom.le, fun h => ⟨neighborhoodHom h⟩⟩

instance {B : OpenBasis X} {x : X} (U V : BasisNeighborhood B x) :
    Subsingleton (U ⟶ V) :=
  ⟨fun f g => ObjectProperty.hom_ext _ (Subsingleton.elim f.hom g.hom)⟩

instance (B : OpenBasis X) (x : X) : Nonempty (BasisNeighborhood B x) := by
  obtain ⟨U, hxU, _⟩ := B.exists_subset ⊤ (x := x) (by trivial)
  exact ⟨⟨op U, hxU⟩⟩

/-- Basis refinement supplies a common successor; intersections need not be basis opens. -/
instance (B : OpenBasis X) (x : X) : IsFiltered (BasisNeighborhood B x) where
  cocone_objs U V := by
    obtain ⟨W, hxW, hW⟩ := B.exists_subset (U.obj.unop.obj ⊓ V.obj.unop.obj)
      (show x ∈ U.obj.unop.obj ⊓ V.obj.unop.obj from ⟨U.property, V.property⟩)
    exact ⟨⟨op W, hxW⟩, neighborhoodHom (hW.trans inf_le_left),
      neighborhoodHom (hW.trans inf_le_right), trivial⟩
  cocone_maps {U V} f g := ⟨V, 𝟙 V, Subsingleton.elim _ _⟩
  nonempty := inferInstance

/-- The original, unlifted restriction diagram on the basis neighborhoods. -/
def neighborhoodDiagram {B : OpenBasis X} (F : RawPresheaf.{u,v} B) (x : X) :
    BasisNeighborhood B x ⥤ AddCommGrpCat.{v} :=
  neighborhoodInclusion B x ⋙ F

@[simp]
theorem neighborhoodDiagram_obj {B : OpenBasis X} (F : RawPresheaf.{u,v} B)
    (x : X) (U : BasisNeighborhood B x) :
    (neighborhoodDiagram F x).obj U = Sections F U.obj.unop := rfl

theorem neighborhoodDiagram_map {B : OpenBasis X} (F : RawPresheaf.{u,v} B)
    {x : X} {U V : BasisNeighborhood B x} (f : U ⟶ V) :
    (neighborhoodDiagram F x).map f = restriction F f.hom.unop.hom.le := by
  congr 1

/-- The restriction diagram lifted to the joint space/value universe. -/
def stalkDiagram {B : OpenBasis X} (F : RawPresheaf.{u,v} B) (x : X) :
    BasisNeighborhood B x ⥤ AddCommGrpCat.{max u v} :=
  neighborhoodDiagram F x ⋙ AddCommGrpCat.uliftFunctor.{u,v}

@[simp]
theorem stalkDiagram_map_apply {B : OpenBasis X} (F : RawPresheaf.{u,v} B)
    {x : X} {U V : BasisNeighborhood B x} (f : U ⟶ V) (s : Sections F U.obj.unop) :
    (stalkDiagram F x).map f (ULift.up s) =
      ULift.up (restriction F f.hom.unop.hom.le s) := by
  change ULift.up ((neighborhoodDiagram F x).map f s) = _
  rw [neighborhoodDiagram_map]
  rfl

/-- Colimit existence follows from the small neighborhood index in the joint universe. -/
theorem hasStalkColimit {B : OpenBasis X} (F : RawPresheaf.{u,v} B) (x : X) :
    HasColimit (stalkDiagram F x) := inferInstance

/-- Restriction and universe lifting are functorial in the original presheaf. -/
def stalkDiagramFunctor (B : OpenBasis X) (x : X) :
    RawPresheaf.{u,v} B ⥤ (BasisNeighborhood B x ⥤ AddCommGrpCat.{max u v}) where
  obj F := stalkDiagram F x
  map φ := whiskerRight (whiskerLeft (neighborhoodInclusion B x) φ)
    AddCommGrpCat.uliftFunctor.{u,v}
  map_id F := by ext U; rfl
  map_comp φ ψ := by ext U; rfl

/-- Taking the actual abelian-group colimit defines the raw stalk functor. -/
noncomputable def rawStalkFunctor (B : OpenBasis X) (x : X) :
    RawPresheaf.{u,v} B ⥤ AddCommGrpCat.{max u v} :=
  stalkDiagramFunctor B x ⋙ colim

/-- The stalk carrier is in `Type (max u v)`. -/
noncomputable abbrev rawStalk {B : OpenBasis X} (F : RawPresheaf.{u,v} B) (x : X) :=
  (rawStalkFunctor B x).obj F

/-- The canonical cocone on the lifted restriction diagram. -/
noncomputable def rawStalkCocone {B : OpenBasis X} (F : RawPresheaf.{u,v} B) (x : X) :
    Cocone (stalkDiagram F x) :=
  colimit.cocone (stalkDiagram F x)

/-- The stalk has the colimit universal property, with no colimit hypothesis. -/
noncomputable def rawStalkIsColimit {B : OpenBasis X} (F : RawPresheaf.{u,v} B) (x : X) :
    IsColimit (rawStalkCocone F x) :=
  colimit.isColimit (stalkDiagram F x)

/-- The additive germ map starts from the original section group. -/
noncomputable def rawGerm {B : OpenBasis X} (F : RawPresheaf.{u,v} B)
    (U : BasisOpen B) (x : X) (hx : x ∈ U.obj) :
    Sections F U →+ rawStalk F x :=
  (colimit.ι (stalkDiagram F x) ⟨op U, hx⟩).hom.comp
    AddEquiv.ulift.symm.toAddMonoidHom

@[simp]
theorem rawGerm_zero {B : OpenBasis X} (F : RawPresheaf.{u,v} B)
    (U : BasisOpen B) (x : X) (hx : x ∈ U.obj) : rawGerm F U x hx 0 = 0 :=
  map_zero _

@[simp]
theorem rawGerm_add {B : OpenBasis X} (F : RawPresheaf.{u,v} B)
    (U : BasisOpen B) (x : X) (hx : x ∈ U.obj) (s t : Sections F U) :
    rawGerm F U x hx (s + t) = rawGerm F U x hx s + rawGerm F U x hx t :=
  map_add _ _ _

/-- Restriction followed by the germ map is the germ on the larger basis open. -/
theorem rawGerm_restriction {B : OpenBasis X} (F : RawPresheaf.{u,v} B)
    {U V : BasisOpen B} (h : U.obj ≤ V.obj) (x : X) (hx : x ∈ U.obj)
    (s : Sections F V) :
    rawGerm F U x hx (restriction F h s) = rawGerm F V x (h hx) s := by
  let f : (⟨op V, h hx⟩ : BasisNeighborhood B x) ⟶ ⟨op U, hx⟩ := neighborhoodHom h
  exact ConcreteCategory.congr_hom (colimit.w (stalkDiagram F x) f) (ULift.up s)

/-- The map on actual colimits induced by an actual natural transformation. -/
noncomputable def rawStalkMap {B : OpenBasis X} {F G : RawPresheaf.{u,v} B}
    (φ : F ⟶ G) (x : X) : rawStalk F x ⟶ rawStalk G x :=
  (rawStalkFunctor B x).map φ

@[simp]
theorem rawStalkMap_id {B : OpenBasis X} (F : RawPresheaf.{u,v} B) (x : X) :
    rawStalkMap (𝟙 F) x = 𝟙 (rawStalk F x) :=
  (rawStalkFunctor B x).map_id F

@[simp]
theorem rawStalkMap_comp {B : OpenBasis X} {F G H : RawPresheaf.{u,v} B}
    (φ : F ⟶ G) (ψ : G ⟶ H) (x : X) :
    rawStalkMap (φ ≫ ψ) x = rawStalkMap φ x ≫ rawStalkMap ψ x :=
  (rawStalkFunctor B x).map_comp φ ψ

/-- Germ naturality evaluated on an original section. -/
theorem rawStalkMap_germ {B : OpenBasis X} {F G : RawPresheaf.{u,v} B}
    (φ : F ⟶ G) (U : BasisOpen B) (x : X) (hx : x ∈ U.obj) (s : Sections F U) :
    rawStalkMap φ x (rawGerm F U x hx s) = rawGerm G U x hx (φ.app (op U) s) := by
  exact ConcreteCategory.congr_hom
    (colimit.ι_map ((stalkDiagramFunctor B x).map φ) ⟨op U, hx⟩) (ULift.up s)

/-- The source-normalized specialization uses its existing category and morphisms. -/
noncomputable def stalkFunctor (B : OpenBasis X) (x : X) :
    Presheaf.{u,v} B ⥤ AddCommGrpCat.{max u v} :=
  presheafInclusion B ⋙ rawStalkFunctor B x

noncomputable abbrev stalk {B : OpenBasis X} (F : Presheaf.{u,v} B) (x : X) :=
  (stalkFunctor B x).obj F

/-- The normalized stalk's canonical cocone on the actual lifted diagram. -/
noncomputable abbrev stalkCocone {B : OpenBasis X} (F : Presheaf.{u,v} B) (x : X) :
    Cocone (stalkDiagram F.obj x) :=
  rawStalkCocone F.obj x

/-- The colimit universal property specialized to a normalized presheaf. -/
noncomputable abbrev stalkIsColimit {B : OpenBasis X} (F : Presheaf.{u,v} B) (x : X) :
    IsColimit (stalkCocone F x) :=
  rawStalkIsColimit F.obj x

/-- The canonical additive germ map on a normalized presheaf. -/
noncomputable abbrev germ {B : OpenBasis X} (F : Presheaf.{u,v} B)
    (U : BasisOpen B) (x : X) (hx : x ∈ U.obj) : Sections F.obj U →+ stalk F x :=
  rawGerm F.obj U x hx

@[simp]
theorem germ_zero {B : OpenBasis X} (F : Presheaf.{u,v} B)
    (U : BasisOpen B) (x : X) (hx : x ∈ U.obj) : germ F U x hx 0 = 0 :=
  map_zero _

@[simp]
theorem germ_add {B : OpenBasis X} (F : Presheaf.{u,v} B)
    (U : BasisOpen B) (x : X) (hx : x ∈ U.obj) (s t : Sections F.obj U) :
    germ F U x hx (s + t) = germ F U x hx s + germ F U x hx t :=
  map_add _ _ _

/-- The normalized germ maps commute with every original restriction. -/
theorem germ_restriction {B : OpenBasis X} (F : Presheaf.{u,v} B)
    {U V : BasisOpen B} (h : U.obj ≤ V.obj) (x : X) (hx : x ∈ U.obj)
    (s : Sections F.obj V) :
    germ F U x hx (restriction F.obj h s) = germ F V x (h hx) s :=
  rawGerm_restriction F.obj h x hx s

/-- The actual induced stalk map in the normalized presheaf category. -/
noncomputable abbrev stalkMap {B : OpenBasis X} {F G : Presheaf.{u,v} B}
    (φ : F ⟶ G) (x : X) : stalk F x ⟶ stalk G x :=
  (stalkFunctor B x).map φ

@[simp]
theorem stalkMap_id {B : OpenBasis X} (F : Presheaf.{u,v} B) (x : X) :
    stalkMap (𝟙 F) x = 𝟙 (stalk F x) :=
  (stalkFunctor B x).map_id F

@[simp]
theorem stalkMap_comp {B : OpenBasis X} {F G H : Presheaf.{u,v} B}
    (φ : F ⟶ G) (ψ : G ⟶ H) (x : X) :
    stalkMap (φ ≫ ψ) x = stalkMap φ x ≫ stalkMap ψ x :=
  (stalkFunctor B x).map_comp φ ψ

theorem stalkMap_germ {B : OpenBasis X} {F G : Presheaf.{u,v} B}
    (φ : F ⟶ G) (U : BasisOpen B) (x : X) (hx : x ∈ U.obj) (s : Sections F.obj U) :
    stalkMap φ x (germ F U x hx s) = germ G U x hx (φ.hom.app (op U) s) :=
  rawStalkMap_germ φ.hom U x hx s

end Langlands.Sheaf.Renard
