import Langlands.Geometry.Analytic.DisjointAffinoidAtlas
import Mathlib.Topology.Category.TopCat.Limits.Basic
import Mathlib.CategoryTheory.Category.Preorder

/-! # Gluing continuous maps on an actual net -/

noncomputable section

universe u v w

namespace Langlands.Analytic.AtlasTopology

open Set CategoryTheory CategoryTheory.Limits

variable {X : Type u} [TopologicalSpace X] {τ : Set (Set X)}

/-- The actual members, ordered by containment. -/
abbrev Member (τ : Set (Set X)) := {U : Set X // U ∈ τ}

theorem IsQuasinet.exists_member (hτ : IsQuasinet τ) (x : X) :
    ∃ U : Member τ, x ∈ U.val := by
  obtain ⟨U, hU, hx⟩ := Set.mem_sUnion.mp
    (show x ∈ ⋃₀ τ from hτ.covers.symm ▸ Set.mem_univ x)
  exact ⟨⟨U, hU⟩, hx⟩

/-- Every point shared by two members lies in a member contained in both. -/
theorem IsNet.exists_common_member (hτ : IsNet τ)
    {U V : Set X} (hU : U ∈ τ) (hV : V ∈ τ)
    {x : X} (hxU : x ∈ U) (hxV : x ∈ V) :
    ∃ W ∈ τ, W ⊆ U ∧ W ⊆ V ∧ x ∈ W := by
  obtain ⟨W, hW, hxW⟩ := Set.mem_sUnion.mp
    (show (⟨x, hxU, hxV⟩ : ↥(U ∩ V)) ∈
        ⋃₀ restrictedFamily τ (U ∩ V) from
      (hτ.2 U hU V hV).covers.symm ▸ Set.mem_univ _)
  obtain ⟨W, hW, hWUV, rfl⟩ := hW
  exact ⟨W, hW, fun y hy => (hWUV hy).1,
    fun y hy => (hWUV hy).2, hxW⟩

/-- Continuous input maps with compatibility under every contained-member inclusion. -/
structure CompatibleMaps (τ : Set (Set X)) (Y : Type v) [TopologicalSpace Y] where
  map : (U : Member τ) → C(U.val, Y)
  comm : ∀ (U V : Member τ) (h : U.val ⊆ V.val) (x : U.val),
    map V (Set.inclusion h x) = map U x

namespace CompatibleMaps

variable {Y : Type v} [TopologicalSpace Y]

@[ext]
theorem ext {f g : CompatibleMaps τ Y} (h : f.map = g.map) : f = g := by
  cases f
  cases g
  cases h
  rfl

/-- Restrict an actual continuous map to every member. -/
def ofMap (f : C(X, Y)) : CompatibleMaps τ Y where
  map _U := ⟨fun x => f x.val, f.continuous.comp continuous_subtype_val⟩
  comm _ _ _ _ := rfl

theorem agree (hτ : IsNet τ) (f : CompatibleMaps τ Y)
    (U V : Member τ) (x : X) (hxU : x ∈ U.val) (hxV : x ∈ V.val) :
    f.map U ⟨x, hxU⟩ = f.map V ⟨x, hxV⟩ := by
  obtain ⟨W, hW, hWU, hWV, hxW⟩ :=
    hτ.exists_common_member U.property V.property hxU hxV
  exact (f.comm ⟨W, hW⟩ U hWU ⟨x, hxW⟩).trans
    (f.comm ⟨W, hW⟩ V hWV ⟨x, hxW⟩).symm

end CompatibleMaps

/-- Choose only an input member containing the point. -/
def IsQuasinet.memberAt (hτ : IsQuasinet τ) (x : X) : Member τ :=
  Classical.choose (hτ.exists_member x)

theorem IsQuasinet.mem_memberAt (hτ : IsQuasinet τ) (x : X) :
    x ∈ (hτ.memberAt x).val :=
  Classical.choose_spec (hτ.exists_member x)

variable {Y : Type v} [TopologicalSpace Y]

/-- The pointwise glued function; compatibility will make the choice immaterial. -/
def IsNet.glueFun (hτ : IsNet τ) (f : CompatibleMaps τ Y) (x : X) : Y :=
  f.map (hτ.1.memberAt x) ⟨x, hτ.1.mem_memberAt x⟩

theorem IsNet.glueFun_apply (hτ : IsNet τ) (f : CompatibleMaps τ Y)
    (U : Member τ) (x : U.val) :
    hτ.glueFun f x.val = f.map U x :=
  f.agree hτ (hτ.1.memberAt x.val) U x.val (hτ.1.mem_memberAt x.val) x.property

/-- The quasinet final-topology property proves continuity of the explicit glue. -/
def IsNet.glue (hτ : IsNet τ) (f : CompatibleMaps τ Y) : C(X, Y) where
  toFun := hτ.glueFun f
  continuous_toFun := by
    apply hτ.1.continuous
    intro U hU
    apply continuousOn_iff_continuous_domRestrict.mpr
    have heq : (fun x : U => hτ.glueFun f x.val) = f.map ⟨U, hU⟩ :=
      funext fun x => hτ.glueFun_apply f ⟨U, hU⟩ x
    change Continuous (fun x : U => hτ.glueFun f x.val)
    rw [heq]
    exact (f.map ⟨U, hU⟩).continuous

@[simp]
theorem IsNet.glue_apply (hτ : IsNet τ) (f : CompatibleMaps τ Y)
    (U : Member τ) (x : U.val) :
    hτ.glue f x.val = f.map U x :=
  hτ.glueFun_apply f U x

theorem IsNet.glue_unique (hτ : IsNet τ) (f : CompatibleMaps τ Y)
    (g : C(X, Y)) (hg : ∀ (U : Member τ) (x : U.val), g x.val = f.map U x) :
    g = hτ.glue f := by
  ext x
  exact hg (hτ.1.memberAt x) ⟨x, hτ.1.mem_memberAt x⟩

/-- Restriction and the constructed glue are inverse, with arbitrary target universe. -/
def IsNet.continuousMapEquiv (hτ : IsNet τ) :
    C(X, Y) ≃ CompatibleMaps τ Y where
  toFun := CompatibleMaps.ofMap
  invFun := hτ.glue
  left_inv f := by
    apply (hτ.glue_unique (CompatibleMaps.ofMap f) f (fun _ _ => rfl)).symm
  right_inv f := by
    apply CompatibleMaps.ext
    funext U
    apply ContinuousMap.ext
    intro x
    exact hτ.glue_apply f U x

/-- Actual member subspaces and their actual continuous inclusions. -/
def memberDiagram (τ : Set (Set X)) : Member τ ⥤ TopCat.{u} where
  obj U := TopCat.of U.val
  map f := TopCat.ofHom
    ⟨Set.inclusion (leOfHom f), continuous_subtype_val.subtype_mk _⟩
  map_id _ := by ext; rfl
  map_comp _ _ := by ext; rfl

/-- The actual inclusions into the original space form a cocone. -/
def memberCocone (τ : Set (Set X)) : Cocone (memberDiagram τ) where
  pt := TopCat.of X
  ι :=
    { app := fun _ => TopCat.ofHom ⟨Subtype.val, continuous_subtype_val⟩
      naturality := by intro U V f; ext; rfl }

/-- A cocone gives precisely the compatible continuous input maps for gluing. -/
def mapsOfCocone (s : Cocone (memberDiagram τ)) : CompatibleMaps τ s.pt where
  map U := (s.ι.app U).hom
  comm U V h x := by
    exact congrArg (fun f : (memberDiagram τ).obj U ⟶ s.pt => f x)
      (s.w (homOfLE h))

/-- The original space is the colimit, without openness or Hausdorff hypotheses. -/
def IsNet.memberCoconeIsColimit (hτ : IsNet τ) :
    IsColimit (memberCocone τ) where
  desc s := TopCat.ofHom (hτ.glue (mapsOfCocone s))
  fac s U := by
    apply TopCat.ext
    intro x
    exact hτ.glue_apply (mapsOfCocone s) U x
  uniq s m hm := by
    apply TopCat.ext
    intro x
    let U := hτ.1.memberAt x
    let y : U.val := ⟨x, hτ.1.mem_memberAt x⟩
    exact (congrArg (fun f : (memberDiagram τ).obj U ⟶ s.pt => f y) (hm U)).trans
      (hτ.glue_apply (mapsOfCocone s) U y).symm

end Langlands.Analytic.AtlasTopology

namespace Langlands.Analytic.IndexedAffinoidAtlas

open CategoryTheory.Limits

variable {K : Type u} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]
  {X : Type v} [TopologicalSpace X] (a : IndexedAffinoidAtlas.{u, v, w} K X)

/-- Topological colimit of the actual chart ranges of the supplied affinoid atlas. -/
def chartRangeCoconeIsColimit :
    IsColimit (AtlasTopology.memberCocone (Set.range (fun i => Set.range (a.chart i)))) :=
  a.isNet_chartFamily.memberCoconeIsColimit

end Langlands.Analytic.IndexedAffinoidAtlas
