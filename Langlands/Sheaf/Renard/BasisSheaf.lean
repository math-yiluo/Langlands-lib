import Langlands.Sheaf.Renard.BasisPresheaf

/-!
# Renard's literal basis sheaf condition

Set-indexed covers give a universe-safe predicate. Its intrinsic gluing law
applies to a family indexed by any type in an independent universe.
-/

open CategoryTheory Opposite TopologicalSpace

universe u v w

namespace Langlands.Sheaf.Renard

variable {X : Type u} [TopologicalSpace X] {B : OpenBasis X}

/-- A family covers a basis open exactly when its members lie inside it and cover its points. -/
def FamilyCovers {ι : Type w} (V : BasisOpen B) (U : ι → BasisOpen B) : Prop :=
  (∀ i, (U i).obj ≤ V.obj) ∧ ∀ x ∈ V.obj, ∃ i, x ∈ (U i).obj

/-- Literal source compatibility: compare on every smaller basis open in an overlap. -/
def Compatible (F : RawPresheaf.{u,v} B) {ι : Type w} (U : ι → BasisOpen B)
    (s : ∀ i, Sections F (U i)) : Prop :=
  ∀ i j (W : BasisOpen B) (hWi : W.obj ≤ (U i).obj) (hWj : W.obj ≤ (U j).obj),
    restriction F hWi (s i) = restriction F hWj (s j)

/-- An actual section whose restrictions are the given family. -/
def IsAmalgamation (F : RawPresheaf.{u,v} B) {ι : Type w} {V : BasisOpen B}
    {U : ι → BasisOpen B} (hU : FamilyCovers V U) (s : ∀ i, Sections F (U i))
    (t : Sections F V) : Prop :=
  ∀ i, restriction F (hU.1 i) t = s i

/-- Transport a section only along equality of its actual basis open. -/
def transportSection (F : RawPresheaf.{u,v} B) {U V : BasisOpen B}
    (h : U = V) (s : Sections F U) : Sections F V := h ▸ s

/-- Transport commutes with restriction to a fixed smaller basis open. -/
theorem restriction_transport (F : RawPresheaf.{u,v} B) {U V W : BasisOpen B}
    (h : U = V) (hWU : W.obj ≤ U.obj) (hWV : W.obj ≤ V.obj) (s : Sections F U) :
    restriction F hWV (transportSection F h s) = restriction F hWU s := by
  cases h
  rfl

/-- Compatibility at the equal open itself identifies duplicate family sections. -/
theorem Compatible.transport_eq (F : RawPresheaf.{u,v} B) {ι : Type w}
    {U : ι → BasisOpen B} {s : ∀ i, Sections F (U i)} (hs : Compatible F U s)
    {i j : ι} (h : U i = U j) : transportSection F h (s i) = s j := by
  have hji : (U j).obj ≤ (U i).obj := by rw [h]
  have heq := hs i j (U j) hji le_rfl
  have hres := restriction_transport F h hji le_rfl (s i)
  simpa using hres.trans heq

/-- The source sheaf axiom for families in a specified, independent index universe. -/
def FamilySheafCondition (F : RawPresheaf.{u,v} B) : Prop :=
  ∀ (ι : Type w) (V : BasisOpen B) (U : ι → BasisOpen B) (hU : FamilyCovers V U)
    (s : ∀ i, Sections F (U i)), Compatible F U s →
      ∃! t : Sections F V, IsAmalgamation F hU s t

/-- A cover encoded by a set of basis opens, without repetitions. -/
structure BasisCover (V : BasisOpen B) where
  members : Set (BasisOpen B)
  le : ∀ U ∈ members, U.obj ≤ V.obj
  covers : ∀ x ∈ V.obj, ∃ U ∈ members, x ∈ U.obj

/-- The subtype-indexed family associated to a set cover is an actual cover. -/
theorem BasisCover.familyCovers {V : BasisOpen B} (C : BasisCover V) :
    FamilyCovers V (fun U : C.members => U.val) := by
  refine ⟨fun U => C.le U.val U.property, ?_⟩
  intro x hx
  obtain ⟨U, hU, hxU⟩ := C.covers x hx
  exact ⟨⟨U, hU⟩, hxU⟩

/-- The universe-safe sheaf condition (F) on all set covers of basis opens. -/
def SheafCondition (F : RawPresheaf.{u,v} B) : Prop :=
  ∀ (V : BasisOpen B) (C : BasisCover V) (s : ∀ U : C.members, Sections F U.val),
    Compatible F (fun U : C.members => U.val) s →
      ∃! t : Sections F V, IsAmalgamation F C.familyCovers s t

/-- Deduplicate an arbitrary indexed cover to its range, a set of actual basis opens. -/
def rangeCover {ι : Type w} {V : BasisOpen B} {U : ι → BasisOpen B}
    (hU : FamilyCovers V U) : BasisCover V where
  members := Set.range U
  le W hW := by
    obtain ⟨i, rfl⟩ := hW
    exact hU.1 i
  covers x hx := by
    obtain ⟨i, hxi⟩ := hU.2 x hx
    exact ⟨U i, Set.mem_range_self i, hxi⟩

/-- Choose an index of an open in the range. This does not bound the index universe. -/
noncomputable def rangeIndex {ι : Type w} (U : ι → BasisOpen B) (W : Set.range U) : ι :=
  Classical.choose W.property

theorem rangeIndex_spec {ι : Type w} (U : ι → BasisOpen B) (W : Set.range U) :
    U (rangeIndex U W) = W.val := Classical.choose_spec W.property

/-- Sections on the range cover, obtained by transporting a chosen representative. -/
noncomputable def rangeSections (F : RawPresheaf.{u,v} B) {ι : Type w}
    (U : ι → BasisOpen B) (s : ∀ i, Sections F (U i))
    (W : Set.range U) : Sections F W.val :=
  transportSection F (rangeIndex_spec U W) (s (rangeIndex U W))

/-- For a compatible family, range sections recover each original section. -/
theorem rangeSections_at (F : RawPresheaf.{u,v} B) {ι : Type w}
    (U : ι → BasisOpen B) (s : ∀ i, Sections F (U i)) (hs : Compatible F U s) (i : ι) :
    rangeSections F U s ⟨U i, Set.mem_range_self i⟩ = s i := by
  exact hs.transport_eq F (rangeIndex_spec U ⟨U i, Set.mem_range_self i⟩)

/-- Transporting representative sections preserves literal overlap compatibility. -/
theorem rangeSections_compatible (F : RawPresheaf.{u,v} B) {ι : Type w}
    (U : ι → BasisOpen B) (s : ∀ i, Sections F (U i)) (hs : Compatible F U s) :
    Compatible F (fun W : Set.range U => W.val) (rangeSections F U s) := by
  intro W Z T hTW hTZ
  let i := rangeIndex U W
  let j := rangeIndex U Z
  have hi : U i = W.val := rangeIndex_spec U W
  have hj : U j = Z.val := rangeIndex_spec U Z
  have hTi : T.obj ≤ (U i).obj := by rw [hi]; exact hTW
  have hTj : T.obj ≤ (U j).obj := by rw [hj]; exact hTZ
  calc
    restriction F hTW (rangeSections F U s W) = restriction F hTi (s i) :=
      restriction_transport F hi hTi hTW (s i)
    _ = restriction F hTj (s j) := hs i j T hTi hTj
    _ = restriction F hTZ (rangeSections F U s Z) :=
      (restriction_transport F hj hTj hTZ (s j)).symm

/-- Set-cover gluing implies actual unique gluing for every index universe, with no size premise. -/
theorem SheafCondition.family (F : RawPresheaf.{u,v} B) (hF : SheafCondition F) :
    FamilySheafCondition.{u,v,w} F := by
  intro ι V U hU s hs
  obtain ⟨t, ht, huniq⟩ := hF V (rangeCover hU) (rangeSections F U s)
    (rangeSections_compatible F U s hs)
  refine ⟨t, ?_, ?_⟩
  · intro i
    exact (ht ⟨U i, Set.mem_range_self i⟩).trans (rangeSections_at F U s hs i)
  · intro y hy
    apply huniq y
    intro W
    obtain ⟨i, hi⟩ := W.property
    have hW : (⟨U i, Set.mem_range_self i⟩ : Set.range U) = W := Subtype.ext hi
    subst W
    exact (hy i).trans (rangeSections_at F U s hs i).symm

/-- Conversely, source-family gluing in the basis-open universe implies set-cover gluing. -/
theorem FamilySheafCondition.sheafCondition (F : RawPresheaf.{u,v} B)
    (hF : FamilySheafCondition.{u,v,u} F) : SheafCondition F := by
  intro V C s hs
  exact hF C.members V (fun U : C.members => U.val) C.familyCovers s hs

/-- The chosen predicate is equivalent to the literal source-family axiom in universe `u`. -/
theorem sheafCondition_iff_family (F : RawPresheaf.{u,v} B) :
    SheafCondition F ↔ FamilySheafCondition.{u,v,u} F :=
  ⟨SheafCondition.family F, FamilySheafCondition.sheafCondition F⟩

/-- An empty index type covers precisely an empty basis open. -/
theorem empty_family_covers_iff {ι : Type w} [IsEmpty ι] (V : BasisOpen B)
    (U : ι → BasisOpen B) : FamilyCovers V U ↔ V.obj = ⊥ := by
  constructor
  · intro hU
    apply bot_unique
    intro x hx
    obtain ⟨i, _⟩ := hU.2 x hx
    exact isEmptyElim i
  · intro hV
    refine ⟨fun i => isEmptyElim i, ?_⟩
    intro x hx
    rw [hV] at hx
    exact False.elim hx

/-- The empty set cover of an empty basis open is included in the chosen predicate. -/
def emptyCover (V : BasisOpen B) (hV : V.obj = ⊥) : BasisCover V where
  members := ∅
  le _ h := False.elim h
  covers x hx := by
    rw [hV] at hx
    exact False.elim hx

/-- Empty-cover gluing already forces the raw presheaf's empty value to be the zero group. -/
theorem SheafCondition.isNormalized (F : RawPresheaf.{u,v} B)
    (hF : SheafCondition F) : IsNormalized F := by
  intro V hV
  let C := emptyCover V hV
  let s : ∀ U : C.members, Sections F U.val := fun U => False.elim U.property
  have hs : Compatible F (fun U : C.members => U.val) s := by
    intro U
    exact False.elim U.property
  obtain ⟨t, _, huniq⟩ := hF V C s hs
  refine ⟨fun a b => (huniq a ?_).trans (huniq b ?_).symm⟩ <;>
    intro U <;> exact False.elim U.property

/-- Normalized presheaves satisfy unique gluing for empty families, even without (F). -/
theorem normalized_empty_gluing (F : Presheaf.{u,v} B) {ι : Type w} [IsEmpty ι]
    {V : BasisOpen B} {U : ι → BasisOpen B} (hU : FamilyCovers V U)
    (s : ∀ i, Sections F.obj (U i)) :
    ∃! t : Sections F.obj V, IsAmalgamation F.obj hU s t := by
  refine ⟨0, fun i => isEmptyElim i, ?_⟩
  intro t _
  exact empty_section_eq_zero F V ((empty_family_covers_iff V U).mp hU) t

/-- The full category of normalized basis presheaves satisfying the source condition (F). -/
abbrev BasisSheaf (B : OpenBasis X) :=
  (show ObjectProperty (Presheaf.{u,v} B) from fun F => SheafCondition F.obj).FullSubcategory

/-- The actual forgetful functor from basis sheaves to normalized basis presheaves. -/
def sheafForget (B : OpenBasis X) : BasisSheaf.{u,v} B ⥤ Presheaf.{u,v} B :=
  ObjectProperty.ι _

instance (B : OpenBasis X) : (sheafForget.{u,v} B).Full :=
  inferInstanceAs (ObjectProperty.ι _).Full

instance (B : OpenBasis X) : (sheafForget.{u,v} B).Faithful :=
  inferInstanceAs (ObjectProperty.ι _).Faithful

/-- Sheaf morphisms are exactly the natural transformations of the underlying functors. -/
def sheafHomEquiv (F G : BasisSheaf.{u,v} B) :
    (F ⟶ G) ≃ (F.obj.obj ⟶ G.obj.obj) :=
  (show (F ⟶ G) ≃ (F.obj ⟶ G.obj) from
    { toFun := fun f => f.hom
      invFun := ObjectProperty.homMk
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }).trans (presheafHomEquiv F.obj G.obj)

/-- A bundled basis sheaf glues any compatible covering family, in every index universe. -/
theorem BasisSheaf.unique_gluing (F : BasisSheaf.{u,v} B) {ι : Type w} (V : BasisOpen B)
    (U : ι → BasisOpen B) (hU : FamilyCovers V U) (s : ∀ i, Sections F.obj.obj (U i))
    (hs : Compatible F.obj.obj U s) :
    ∃! t : Sections F.obj.obj V, IsAmalgamation F.obj.obj hU s t :=
  SheafCondition.family F.obj.obj F.property ι V U hU s hs

end Langlands.Sheaf.Renard
