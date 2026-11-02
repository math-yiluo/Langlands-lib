import Langlands.Sheaf.Renard.BasisStalk
import Mathlib.Algebra.Group.Pi.Basic
import Mathlib.Algebra.Group.Subgroup.Basic

/-!
# Locally represented families of original stalk germs

The families are defined on every actual open, with independent space and
original-value universes. Local representation holds on a whole neighborhood.
-/

open CategoryTheory Opposite TopologicalSpace

universe u v w

namespace Langlands.Sheaf.Renard

variable {X : Type u} [TopologicalSpace X] {B : OpenBasis X}

/-- A section of the disjoint stalk union, expressed as a dependent family. -/
noncomputable abbrev GermFamily (F : RawPresheaf.{u,v} B) (U : Opens X) :=
  (x : U) → rawStalk F x.val

/-- Original sections represent the family on an entire contained basis neighborhood. -/
def LocallyRepresented (F : RawPresheaf.{u,v} B) (U : Opens X)
    (s : GermFamily F U) : Prop :=
  ∀ x : U, ∃ (V : BasisOpen B) (_hx : x.val ∈ V.obj) (hVU : V.obj ≤ U)
    (t : Sections F V),
    ∀ (y : X) (hy : y ∈ V.obj), rawGerm F V y hy t = s ⟨y, hVU hy⟩

/-- The source cover form permits the representing opens to extend outside the domain. -/
def RepresentedOnCover (F : RawPresheaf.{u,v} B) (U : Opens X)
    (s : GermFamily F U) {ι : Type w} (V : ι → BasisOpen B)
    (t : ∀ i, Sections F (V i)) : Prop :=
  (∀ x : U, ∃ i, x.val ∈ (V i).obj) ∧
    ∀ (i : ι) (x : U) (hx : x.val ∈ (V i).obj),
      rawGerm F (V i) x.val hx (t i) = s x

/-- Refine a source cover at each point and restrict its original representing section. -/
theorem locallyRepresented_of_cover (F : RawPresheaf.{u,v} B) (U : Opens X)
    (s : GermFamily F U) {ι : Type w} (V : ι → BasisOpen B)
    (t : ∀ i, Sections F (V i)) (h : RepresentedOnCover F U s V t) :
    LocallyRepresented F U s := by
  intro x
  obtain ⟨i, hxi⟩ := h.1 x
  obtain ⟨W, hxW, hW⟩ := B.exists_subset ((V i).obj ⊓ U) ⟨hxi, x.property⟩
  let hWi : W.obj ≤ (V i).obj := hW.trans inf_le_left
  let hWU : W.obj ≤ U := hW.trans inf_le_right
  refine ⟨W, hxW, hWU, restriction F hWi (t i), ?_⟩
  intro y hy
  exact (rawGerm_restriction F hWi y hy (t i)).trans
    (h.2 i ⟨y, hWU hy⟩ (hWi hy))

/-- Local witnesses give a contained basis cover indexed by the points of the open. -/
theorem LocallyRepresented.cover (F : RawPresheaf.{u,v} B) (U : Opens X)
    {s : GermFamily F U} (h : LocallyRepresented F U s) :
    ∃ (V : U → BasisOpen B) (t : ∀ x, Sections F (V x)),
      (∀ x, (V x).obj ≤ U) ∧ RepresentedOnCover F U s V t := by
  classical
  choose V hx hVU t ht using h
  refine ⟨V, t, hVU, (fun x => ⟨x, hx x⟩), ?_⟩
  intro i x hxi
  exact ht i x.val hxi

/-- The contained-neighborhood and source-cover descriptions define the same families. -/
theorem locallyRepresented_iff_cover (F : RawPresheaf.{u,v} B) (U : Opens X)
    (s : GermFamily F U) :
    LocallyRepresented F U s ↔
      ∃ (V : U → BasisOpen B) (t : ∀ x, Sections F (V x)),
        (∀ x, (V x).obj ≤ U) ∧ RepresentedOnCover F U s V t :=
  ⟨LocallyRepresented.cover F U, fun ⟨V, t, _, ht⟩ =>
    locallyRepresented_of_cover F U s V t ht⟩

theorem locallyRepresented_zero (F : RawPresheaf.{u,v} B) (U : Opens X) :
    LocallyRepresented F U 0 := by
  intro x
  obtain ⟨V, hxV, hVU⟩ := B.exists_subset U x.property
  exact ⟨V, hxV, hVU, 0, fun y hy => rawGerm_zero F V y hy⟩

/-- Addition uses a common smaller basis open and adds the restricted original sections. -/
theorem LocallyRepresented.add (F : RawPresheaf.{u,v} B) (U : Opens X)
    {s t : GermFamily F U} (hs : LocallyRepresented F U s)
    (ht : LocallyRepresented F U t) : LocallyRepresented F U (s + t) := by
  intro x
  obtain ⟨V, hxV, hVU, a, ha⟩ := hs x
  obtain ⟨W, hxW, hWU, b, hb⟩ := ht x
  obtain ⟨T, hxT, hT⟩ := B.exists_subset (V.obj ⊓ W.obj) ⟨hxV, hxW⟩
  let hTV : T.obj ≤ V.obj := hT.trans inf_le_left
  let hTW : T.obj ≤ W.obj := hT.trans inf_le_right
  refine ⟨T, hxT, hTV.trans hVU,
    restriction F hTV a + restriction F hTW b, ?_⟩
  intro y hy
  change rawGerm F T y hy _ =
    s ⟨y, hVU (hTV hy)⟩ + t ⟨y, hVU (hTV hy)⟩
  rw [map_add, rawGerm_restriction, rawGerm_restriction, ha, hb]

theorem LocallyRepresented.neg (F : RawPresheaf.{u,v} B) (U : Opens X)
    {s : GermFamily F U} (hs : LocallyRepresented F U s) :
    LocallyRepresented F U (-s) := by
  intro x
  obtain ⟨V, hxV, hVU, a, ha⟩ := hs x
  refine ⟨V, hxV, hVU, -a, ?_⟩
  intro y hy
  change rawGerm F V y hy (-a) = -(s ⟨y, hVU hy⟩)
  rw [map_neg, ha]

/-- The actual additive subgroup of locally represented dependent families. -/
noncomputable def germSectionSubgroup (F : RawPresheaf.{u,v} B) (U : Opens X) :
    AddSubgroup (GermFamily F U) where
  carrier := {s | LocallyRepresented F U s}
  zero_mem' := locallyRepresented_zero F U
  add_mem' := LocallyRepresented.add F U
  neg_mem' := LocallyRepresented.neg F U

/-- The section carrier has the inherited pointwise abelian-group structure. -/
noncomputable abbrev GermSections (F : RawPresheaf.{u,v} B) (U : Opens X) :
    Type (max u v) :=
  ↥(germSectionSubgroup F U)

@[ext]
theorem GermSections.ext {F : RawPresheaf.{u,v} B} {U : Opens X}
    {s t : GermSections F U} (h : ∀ x : U, s.val x = t.val x) : s = t :=
  Subtype.ext (funext h)

@[simp]
theorem germSections_zero_apply (F : RawPresheaf.{u,v} B) (U : Opens X) (x : U) :
    (0 : GermSections F U).val x = 0 := rfl

@[simp]
theorem germSections_add_apply {F : RawPresheaf.{u,v} B} {U : Opens X}
    (s t : GermSections F U) (x : U) : (s + t).val x = s.val x + t.val x := rfl

@[simp]
theorem germSections_neg_apply {F : RawPresheaf.{u,v} B} {U : Opens X}
    (s : GermSections F U) (x : U) : (-s).val x = -s.val x := rfl

/-- Restrict a family to any smaller actual open, refining local original representatives. -/
theorem LocallyRepresented.restrict (F : RawPresheaf.{u,v} B)
    {U V : Opens X} (h : U ≤ V) {s : GermFamily F V} (hs : LocallyRepresented F V s) :
    LocallyRepresented F U (fun x => s ⟨x.val, h x.property⟩) := by
  intro x
  obtain ⟨W, hxW, hWV, a, ha⟩ := hs ⟨x.val, h x.property⟩
  obtain ⟨T, hxT, hT⟩ := B.exists_subset (W.obj ⊓ U) ⟨hxW, x.property⟩
  let hTW : T.obj ≤ W.obj := hT.trans inf_le_left
  let hTU : T.obj ≤ U := hT.trans inf_le_right
  refine ⟨T, hxT, hTU, restriction F hTW a, ?_⟩
  intro y hy
  exact (rawGerm_restriction F hTW y hy a).trans (ha y (hTW hy))

/-- The additive restriction is actual restriction of dependent functions. -/
noncomputable def germRestriction (F : RawPresheaf.{u,v} B)
    {U V : Opens X} (h : U ≤ V) : GermSections F V →+ GermSections F U where
  toFun s := ⟨fun x => s.val ⟨x.val, h x.property⟩,
    LocallyRepresented.restrict F h s.property⟩
  map_zero' := rfl
  map_add' _ _ := rfl

@[simp]
theorem germRestriction_apply (F : RawPresheaf.{u,v} B)
    {U V : Opens X} (h : U ≤ V) (s : GermSections F V) (x : U) :
    (germRestriction F h s).val x = s.val ⟨x.val, h x.property⟩ := rfl

@[simp]
theorem germRestriction_self (F : RawPresheaf.{u,v} B) (U : Opens X) :
    germRestriction F (le_refl U) = AddMonoidHom.id (GermSections F U) := rfl

theorem germRestriction_comp (F : RawPresheaf.{u,v} B) {U V W : Opens X}
    (hUV : U ≤ V) (hVW : V ≤ W) :
    (germRestriction F hUV).comp (germRestriction F hVW) =
      germRestriction F (hUV.trans hVW) := rfl

instance germSections_empty_subsingleton (F : RawPresheaf.{u,v} B) :
    Subsingleton (GermSections F (⊥ : Opens X)) :=
  ⟨fun _s _t => GermSections.ext (fun x => False.elim x.property)⟩

/-- Apply the original natural transformation on each stalk. -/
theorem LocallyRepresented.map {F G : RawPresheaf.{u,v} B} (φ : F ⟶ G)
    (U : Opens X) {s : GermFamily F U} (hs : LocallyRepresented F U s) :
    LocallyRepresented G U (fun x => rawStalkMap φ x.val (s x)) := by
  intro x
  obtain ⟨V, hxV, hVU, t, ht⟩ := hs x
  refine ⟨V, hxV, hVU, φ.app (op V) t, ?_⟩
  intro y hy
  rw [← rawStalkMap_germ, ht]

/-- The induced map is the pointwise additive stalk map. -/
noncomputable def germSectionsMap {F G : RawPresheaf.{u,v} B} (φ : F ⟶ G)
    (U : Opens X) : GermSections F U →+ GermSections G U where
  toFun s := ⟨fun x => rawStalkMap φ x.val (s.val x),
    LocallyRepresented.map φ U s.property⟩
  map_zero' := by apply GermSections.ext; intro x; exact map_zero _
  map_add' s t := by apply GermSections.ext; intro x; exact map_add _ _ _

@[simp]
theorem germSectionsMap_apply {F G : RawPresheaf.{u,v} B} (φ : F ⟶ G)
    (U : Opens X) (s : GermSections F U) (x : U) :
    (germSectionsMap φ U s).val x = rawStalkMap φ x.val (s.val x) := rfl

/-- On every original local representative the image has precisely the expected germ. -/
theorem germSectionsMap_representative {F G : RawPresheaf.{u,v} B} (φ : F ⟶ G)
    {U : Opens X} (s : GermSections F U) (V : BasisOpen B)
    (hVU : V.obj ≤ U) (t : Sections F V)
    (ht : ∀ (y : X) (hy : y ∈ V.obj), rawGerm F V y hy t = s.val ⟨y, hVU hy⟩)
    (y : X) (hy : y ∈ V.obj) :
    (germSectionsMap φ U s).val ⟨y, hVU hy⟩ =
      rawGerm G V y hy (φ.app (op V) t) := by
  change rawStalkMap φ y (s.val ⟨y, hVU hy⟩) = _
  rw [← ht y hy, rawStalkMap_germ]

theorem germSectionsMap_restriction {F G : RawPresheaf.{u,v} B} (φ : F ⟶ G)
    {U V : Opens X} (h : U ≤ V) :
    (germSectionsMap φ U).comp (germRestriction F h) =
      (germRestriction G h).comp (germSectionsMap φ V) := rfl

@[simp]
theorem germSectionsMap_id (F : RawPresheaf.{u,v} B) (U : Opens X) :
    germSectionsMap (𝟙 F) U = AddMonoidHom.id (GermSections F U) := by
  ext s x
  exact ConcreteCategory.congr_hom (rawStalkMap_id F x.val) (s.val x)

theorem germSectionsMap_comp {F G H : RawPresheaf.{u,v} B}
    (φ : F ⟶ G) (ψ : G ⟶ H) (U : Opens X) :
    germSectionsMap (φ ≫ ψ) U = (germSectionsMap ψ U).comp (germSectionsMap φ U) := by
  ext s x
  exact ConcreteCategory.congr_hom (rawStalkMap_comp φ ψ x.val) (s.val x)

end Langlands.Sheaf.Renard
