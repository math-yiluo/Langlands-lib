import Langlands.Sheaf.Renard.BasisRestriction
import Langlands.Sheaf.Renard.BasisStalkRepresentatives
import Mathlib.CategoryTheory.Filtered.Final

/-!
# Stalks before and after restricting an all-open presheaf to a chosen basis

Chosen basis neighborhoods of a point are final among all actual open
neighborhoods, by basis refinement. The map they induce between the two
actual stalk colimits is therefore an isomorphism, sending each restricted
germ to the germ of the same original section.
-/

open CategoryTheory CategoryTheory.Functor CategoryTheory.Limits Opposite TopologicalSpace

universe u v

namespace Langlands.Sheaf.Renard

variable {X : Type u} [TopologicalSpace X]

/-- A chosen basis neighborhood of `x`, regarded as an actual open neighborhood of `x`. -/
def neighborhoodToAllOpen (B : OpenBasis X) (x : X) :
    BasisNeighborhood B x ⥤ BasisNeighborhood (allOpenBasis X) x where
  obj U := ⟨op (allOpen U.obj.unop.obj), U.property⟩
  map f := ObjectProperty.homMk ((basisToAllOpen B).op.map f.hom)
  map_id _ := rfl
  map_comp _ _ := rfl

@[simp]
theorem neighborhoodToAllOpen_obj (B : OpenBasis X) (x : X) (U : BasisNeighborhood B x) :
    ((neighborhoodToAllOpen B x).obj U).obj = op (allOpen U.obj.unop.obj) := rfl

/-- The neighborhood functor lies over the actual basis inclusion. -/
theorem neighborhoodToAllOpen_comp_inclusion (B : OpenBasis X) (x : X) :
    neighborhoodToAllOpen B x ⋙ neighborhoodInclusion (allOpenBasis X) x =
      neighborhoodInclusion B x ⋙ (basisToAllOpen B).op := rfl

/-- The stalk diagram of the restriction is literally the original diagram on basis
neighborhoods. -/
theorem stalkDiagram_rawBasisRestriction (B : OpenBasis X)
    (F : RawPresheaf.{u,v} (allOpenBasis X)) (x : X) :
    stalkDiagram ((rawBasisRestriction B).obj F) x =
      neighborhoodToAllOpen B x ⋙ stalkDiagram F x := rfl

/-- Basis refinement: every actual open neighborhood contains a chosen basis neighborhood. -/
theorem exists_neighborhoodToAllOpen_hom (B : OpenBasis X) (x : X)
    (W : BasisNeighborhood (allOpenBasis X) x) :
    ∃ V : BasisNeighborhood B x, Nonempty (W ⟶ (neighborhoodToAllOpen B x).obj V) := by
  obtain ⟨V, hxV, hVW⟩ := B.exists_subset W.obj.unop.obj W.property
  exact ⟨⟨op V, hxV⟩, ⟨neighborhoodHom hVW⟩⟩

/-- Chosen basis neighborhoods are final among actual open neighborhoods. This is proved
from basis refinement, the published filteredness of the chosen basis neighborhoods, and
thinness of the all-open neighborhood category. -/
instance neighborhoodToAllOpen_final (B : OpenBasis X) (x : X) :
    (neighborhoodToAllOpen B x).Final :=
  Functor.final_of_exists_of_isFiltered _ (exists_neighborhoodToAllOpen_hom B x)
    (fun {_ c} _ _ => ⟨c, 𝟙 c, Subsingleton.elim _ _⟩)

/-- The canonical isomorphism between the two actual stalk colimits. Its forward map is
the colimit comparison `colimit.pre` along the neighborhood functor. -/
noncomputable def rawStalkRestrictionIso (B : OpenBasis X)
    (F : RawPresheaf.{u,v} (allOpenBasis X)) (x : X) :
    rawStalk ((rawBasisRestriction B).obj F) x ≅ rawStalk F x :=
  Functor.Final.colimitIso (neighborhoodToAllOpen B x) (stalkDiagram F x)

theorem rawStalkRestrictionIso_hom (B : OpenBasis X)
    (F : RawPresheaf.{u,v} (allOpenBasis X)) (x : X) :
    (rawStalkRestrictionIso B F x).hom =
      colimit.pre (stalkDiagram F x) (neighborhoodToAllOpen B x) := rfl

/-- The additive isomorphism `c_(B,F,x)` of the actual stalks. -/
noncomputable def rawStalkRestrictionEquiv (B : OpenBasis X)
    (F : RawPresheaf.{u,v} (allOpenBasis X)) (x : X) :
    rawStalk ((rawBasisRestriction B).obj F) x ≃+ rawStalk F x :=
  (rawStalkRestrictionIso B F x).addCommGroupIsoToAddEquiv

theorem rawStalkRestrictionEquiv_apply (B : OpenBasis X)
    (F : RawPresheaf.{u,v} (allOpenBasis X)) (x : X)
    (a : rawStalk ((rawBasisRestriction B).obj F) x) :
    rawStalkRestrictionEquiv B F x a = (rawStalkRestrictionIso B F x).hom a := rfl

theorem rawStalkRestrictionEquiv_symm_apply (B : OpenBasis X)
    (F : RawPresheaf.{u,v} (allOpenBasis X)) (x : X) (a : rawStalk F x) :
    (rawStalkRestrictionEquiv B F x).symm a = (rawStalkRestrictionIso B F x).inv a := rfl

/-- The comparison sends the restricted germ of an original section to its original germ. -/
@[simp]
theorem rawStalkRestrictionEquiv_germ (B : OpenBasis X)
    (F : RawPresheaf.{u,v} (allOpenBasis X)) (V : BasisOpen B) (x : X) (hx : x ∈ V.obj)
    (t : Sections F (allOpen V.obj)) :
    rawStalkRestrictionEquiv B F x (rawGerm ((rawBasisRestriction B).obj F) V x hx t) =
      rawGerm F (allOpen V.obj) x hx t :=
  ConcreteCategory.congr_hom
    (Functor.Final.ι_colimitIso_hom (neighborhoodToAllOpen B x) (stalkDiagram F x)
      ⟨op V, hx⟩) (ULift.up t)

/-- The inverse sends the original germ on a basis open to the restricted germ. -/
@[simp]
theorem rawStalkRestrictionEquiv_symm_germ (B : OpenBasis X)
    (F : RawPresheaf.{u,v} (allOpenBasis X)) (V : BasisOpen B) (x : X) (hx : x ∈ V.obj)
    (t : Sections F (allOpen V.obj)) :
    (rawStalkRestrictionEquiv B F x).symm (rawGerm F (allOpen V.obj) x hx t) =
      rawGerm ((rawBasisRestriction B).obj F) V x hx t := by
  rw [AddEquiv.symm_apply_eq, rawStalkRestrictionEquiv_germ]

/-- The inverse on an arbitrary actual open: restrict to any smaller chosen basis
neighborhood of the point. -/
theorem rawStalkRestrictionEquiv_symm_germ_of_le (B : OpenBasis X)
    (F : RawPresheaf.{u,v} (allOpenBasis X)) {W : BasisOpen (allOpenBasis X)}
    (V : BasisOpen B) (h : V.obj ≤ W.obj) (x : X) (hx : x ∈ V.obj)
    (t : Sections F W) :
    (rawStalkRestrictionEquiv B F x).symm (rawGerm F W x (h hx) t) =
      rawGerm ((rawBasisRestriction B).obj F) V x hx
        (restriction F (U := allOpen V.obj) h t) := by
  rw [← rawGerm_restriction F (U := allOpen V.obj) h x hx t,
    rawStalkRestrictionEquiv_symm_germ]

/-- Naturality of the comparison for an original natural transformation. -/
theorem rawStalkRestrictionEquiv_naturality (B : OpenBasis X)
    {F G : RawPresheaf.{u,v} (allOpenBasis X)} (φ : F ⟶ G) (x : X)
    (a : rawStalk ((rawBasisRestriction B).obj F) x) :
    rawStalkRestrictionEquiv B G x (rawStalkMap ((rawBasisRestriction B).map φ) x a) =
      rawStalkMap φ x (rawStalkRestrictionEquiv B F x a) := by
  obtain ⟨V, hx, t, rfl⟩ := rawStalk_representative ((rawBasisRestriction B).obj F) x a
  rw [rawStalkMap_germ]
  exact (rawStalkRestrictionEquiv_germ B G V x hx (φ.app (op (allOpen V.obj)) t)).trans
    ((rawStalkMap_germ φ (allOpen V.obj) x hx t).symm.trans
      (congrArg (rawStalkMap φ x) (rawStalkRestrictionEquiv_germ B F V x hx t).symm))

/-- Naturality of the inverse comparison. -/
theorem rawStalkRestrictionEquiv_symm_naturality (B : OpenBasis X)
    {F G : RawPresheaf.{u,v} (allOpenBasis X)} (φ : F ⟶ G) (x : X) (a : rawStalk F x) :
    (rawStalkRestrictionEquiv B G x).symm (rawStalkMap φ x a) =
      rawStalkMap ((rawBasisRestriction B).map φ) x ((rawStalkRestrictionEquiv B F x).symm a) := by
  rw [AddEquiv.symm_apply_eq, rawStalkRestrictionEquiv_naturality, AddEquiv.apply_symm_apply]

/-- Naturality as a commutative square of actual stalk maps. -/
theorem rawStalkRestrictionIso_hom_naturality (B : OpenBasis X)
    {F G : RawPresheaf.{u,v} (allOpenBasis X)} (φ : F ⟶ G) (x : X) :
    rawStalkMap ((rawBasisRestriction B).map φ) x ≫ (rawStalkRestrictionIso B G x).hom =
      (rawStalkRestrictionIso B F x).hom ≫ rawStalkMap φ x := by
  apply AddCommGrpCat.ext
  intro a
  exact rawStalkRestrictionEquiv_naturality B φ x a

/-- The comparison as a natural isomorphism of actual stalk functors. -/
noncomputable def rawStalkRestrictionNatIso (B : OpenBasis X) (x : X) :
    rawBasisRestriction.{u,v} B ⋙ rawStalkFunctor B x ≅
      rawStalkFunctor (allOpenBasis X) x :=
  NatIso.ofComponents (fun F => rawStalkRestrictionIso B F x)
    (fun φ => rawStalkRestrictionIso_hom_naturality B φ x)

@[simp]
theorem rawStalkRestrictionNatIso_app (B : OpenBasis X)
    (F : RawPresheaf.{u,v} (allOpenBasis X)) (x : X) :
    (rawStalkRestrictionNatIso B x).app F = rawStalkRestrictionIso B F x := rfl

/-- The source-normalized specialization, by precomposing with the existing inclusion. -/
noncomputable def stalkRestrictionNatIso (B : OpenBasis X) (x : X) :
    basisRestriction.{u,v} B ⋙ stalkFunctor B x ≅ stalkFunctor (allOpenBasis X) x :=
  isoWhiskerLeft (presheafInclusion (allOpenBasis X)) (rawStalkRestrictionNatIso B x)

@[simp]
theorem stalkRestrictionNatIso_app (B : OpenBasis X)
    (F : Presheaf.{u,v} (allOpenBasis X)) (x : X) :
    (stalkRestrictionNatIso B x).app F = rawStalkRestrictionIso B F.obj x := rfl

end Langlands.Sheaf.Renard
