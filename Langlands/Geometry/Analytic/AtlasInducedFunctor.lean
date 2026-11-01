import Langlands.Geometry.Analytic.AtlasInducedAction

/-! # Functorial full bounded induction of arbitrary atlas actions -/

noncomputable section

universe u v w z

namespace Langlands.Analytic.AtlasInducedAction

open CategoryTheory
open PresentedAffinoidAlgebra.InducedAction

variable {K : Type u} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]
  {G : Type z} [Group G] (H : Subgroup G)
  {X Y Z : Action (AffinoidAtlasPresentation.{u, max z v, max z w} K) H}

/-- Retain the original equivariant arrow on the original nonempty charts. -/
abbrev localMap (f : X ⟶ Y) : X.V.nonemptyPresentation ⟶ Y.V.nonemptyPresentation :=
  f.hom.nonemptyMap

/-- Equivariance survives restriction as equality of complete bounded arrows. -/
theorem localMap_equivariant (f : X ⟶ Y) (h : H) :
    localAction H X h ≫ localMap H f = localMap H f ≫ localAction H Y h := by
  unfold localAction localMap
  rw [← AffinoidAtlasPresentation.Hom.nonemptyMap_comp,
    ← AffinoidAtlasPresentation.Hom.nonemptyMap_comp, f.comm h]

/-- Apply the given full arrow inside each coset copy, keeping the coset tag. -/
def copiesMap (f : X ⟶ Y) : copies H X ⟶ copies H Y :=
  AtlasDisjointUnion.map (component H X) (component_hasNonemptyCharts H X)
    (component H Y) (component_hasNonemptyCharts H Y)
    _root_.id (fun _ => localMap H f)

@[simp]
theorem copy_map (f : X ⟶ Y) (c : G ⧸ H) :
    copy H X c ≫ copiesMap H f = localMap H f ≫ copy H Y c :=
  AtlasDisjointUnion.inclusion_map _ _ _ _ _ _ c

@[simp]
theorem copiesMap_baseMap (f : X ⟶ Y) (c : G ⧸ H) (x : X.V.space) :
    (copiesMap H f).baseMap ⟨c, x⟩ = ⟨c, f.hom.baseMap x⟩ := rfl

@[simp]
theorem copiesMap_indexMap (f : X ⟶ Y) (c : G ⧸ H)
    (i : X.V.nonemptyPresentation.atlas.Index) :
    (copiesMap H f).indexMap ⟨c, i⟩ = ⟨c, (localMap H f).indexMap i⟩ := rfl

/-- The actual bounded pullback is precisely the original one. -/
@[simp]
theorem copiesMap_pullback (f : X ⟶ Y) (c : G ⧸ H)
    (i : X.V.nonemptyPresentation.atlas.Index) :
    (copiesMap H f).pullback ⟨c, i⟩ = f.hom.pullback i.val :=
  AtlasDisjointUnion.map_pullback (component H X) (component_hasNonemptyCharts H X)
    (component H Y) (component_hasNonemptyCharts H Y)
    _root_.id (fun _ => localMap H f) c i

/-- The correction action commutes with the entire constructed arrow. -/
theorem copiesMap_equivariant (f : X ⟶ Y) (g : G) :
    copiesActionMap H X g ≫ copiesMap H f =
      copiesMap H f ≫ copiesActionMap H Y g := by
  apply AtlasDisjointUnion.hom_ext (component H X) (component_hasNonemptyCharts H X)
  intro c
  change copy H X c ≫ (copiesActionMap H X g ≫ copiesMap H f) =
    copy H X c ≫ (copiesMap H f ≫ copiesActionMap H Y g)
  rw [← Category.assoc, copy_action, Category.assoc, copy_map,
    ← Category.assoc, localMap_equivariant, Category.assoc,
    ← copy_action, ← Category.assoc, ← copy_map, Category.assoc]

@[simp]
theorem copiesMap_id (X : Action (AffinoidAtlasPresentation.{u, max z v, max z w} K) H) :
    copiesMap H (𝟙 X) = 𝟙 (copies H X) := by
  apply AtlasDisjointUnion.hom_ext (component H X) (component_hasNonemptyCharts H X)
  intro c
  change copy H X c ≫ copiesMap H (𝟙 X) = copy H X c ≫ 𝟙 _
  simp only [copy_map, localMap, Action.id_hom,
    AffinoidAtlasPresentation.Hom.nonemptyMap_id, Category.id_comp, Category.comp_id]

/-- Functoriality retains all chosen indices and dependent bounded pullbacks. -/
theorem copiesMap_comp (f : X ⟶ Y) (k : Y ⟶ Z) :
    copiesMap H (f ≫ k) = copiesMap H f ≫ copiesMap H k := by
  apply AtlasDisjointUnion.hom_ext (component H X) (component_hasNonemptyCharts H X)
  intro c
  change copy H X c ≫ copiesMap H (f ≫ k) =
    copy H X c ≫ (copiesMap H f ≫ copiesMap H k)
  rw [copy_map, ← Category.assoc, copy_map, Category.assoc, copy_map]
  simp only [localMap, Action.comp_hom,
    AffinoidAtlasPresentation.Hom.nonemptyMap_comp, Category.assoc]

/-- Induction on equivariant arrows in the chosen bounded atlas category. -/
def copiesEquivariantMap (f : X ⟶ Y) : copiesAction H X ⟶ copiesAction H Y where
  hom := copiesMap H f
  comm := copiesMap_equivariant H f

/-- Algebraic coset-copy induction is a functor on all supplied atlas actions. -/
def copiesFunctor :
    Action (AffinoidAtlasPresentation.{u, max z v, max z w} K) H ⥤
      Action (AffinoidAtlasPresentation.{u, max z v, max z w} K) G where
  obj := copiesAction H
  map := copiesEquivariantMap H
  map_id X := Action.Hom.ext (copiesMap_id H X)
  map_comp f k := Action.Hom.ext (copiesMap_comp H f k)

end Langlands.Analytic.AtlasInducedAction
