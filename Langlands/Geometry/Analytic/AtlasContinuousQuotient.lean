import Langlands.Geometry.Analytic.PointContinuousAtlasActions
import Langlands.Geometry.Analytic.AtlasInducedQuotient

/-! # Balanced-quotient induction on full jointly point-continuous atlas actions -/

noncomputable section

universe u v w z

namespace Langlands.Analytic.AtlasInducedAction

open CategoryTheory Topology

variable {K : Type u} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]
  {G : Type z} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  (H : Subgroup G) (hH : IsOpen (H : Set G))

omit [IsTopologicalGroup G] in
/-- Derive the precise source continuity instance from the stated joint point condition. -/
theorem sourceContinuousSMul
    (X : PointContinuousNonemptyAtlasAction.{u, max z v, max z w, z} K H) :
    ContinuousSMul H (LocalSpace H X.obj) :=
  ⟨X.property.2⟩

attribute [local instance] sourceContinuousSMul

/-- The full quotient atlas inherits its actual unchanged chart algebras. -/
theorem quotient_hasNonemptyCharts
    (X : PointContinuousNonemptyAtlasAction.{u, max z v, max z w, z} K H) :
    (presentation H X.obj hH).atlas.HasNonemptyCharts :=
  fun i => i.2.property

/-- The constructed bounded quotient action, with its proved joint continuity. -/
def pointContinuousQuotient
    (X : PointContinuousNonemptyAtlasAction.{u, max z v, max z w, z} K H) :
    PointContinuousNonemptyAtlasAction.{u, max z v, max z w, z} K G :=
  ⟨action H X.obj hH,
    ⟨quotient_hasNonemptyCharts H hH X, continuous_action H X.obj hH⟩⟩

/-- Induce all original complete equivariant bounded arrows on the actual quotients. -/
def pointContinuousQuotientFunctor :
    PointContinuousNonemptyAtlasAction.{u, max z v, max z w, z} K H ⥤
      PointContinuousNonemptyAtlasAction.{u, max z v, max z w, z} K G where
  obj := pointContinuousQuotient H hH
  map f := ObjectProperty.homMk (quotientEquivariantMap H hH f.hom)
  map_id X := by
    apply ObjectProperty.hom_ext
    apply Action.Hom.ext
    exact quotientMap_id H hH
  map_comp f k := by
    apply ObjectProperty.hom_ext
    apply Action.Hom.ext
    exact quotientMap_comp H hH f.hom k.hom

@[simp]
theorem pointContinuousQuotientFunctor_obj
    (X : PointContinuousNonemptyAtlasAction.{u, max z v, max z w, z} K H) :
    ((pointContinuousQuotientFunctor H hH).obj X).obj = action H X.obj hH := rfl

@[simp]
theorem pointContinuousQuotientFunctor_map
    {X Y : PointContinuousNonemptyAtlasAction.{u, max z v, max z w, z} K H}
    (f : X ⟶ Y) :
    ((pointContinuousQuotientFunctor H hH).map f).hom =
      quotientEquivariantMap H hH f.hom := rfl

/-- The induced point map is the original equivariant map on each representative. -/
theorem pointContinuousQuotientFunctor_map_mk
    {X Y : PointContinuousNonemptyAtlasAction.{u, max z v, max z w, z} K H}
    (f : X ⟶ Y) (g : G) (x : LocalSpace H X.obj) :
    ((pointContinuousQuotientFunctor H hH).map f).hom.hom.baseMap
        (TopologicalInduction.mk H g x) =
      TopologicalInduction.mk H g
        (show LocalSpace H Y.obj from f.hom.hom.baseMap x) :=
  quotientMap_mk H hH f.hom g x

/-- The original chosen target index is retained, with its coset tag. -/
theorem pointContinuousQuotientFunctor_map_index
    {X Y : PointContinuousNonemptyAtlasAction.{u, max z v, max z w, z} K H}
    (f : X ⟶ Y) (c : G ⧸ H) (i : X.obj.V.nonemptyPresentation.atlas.Index) :
    ((pointContinuousQuotientFunctor H hH).map f).hom.hom.indexMap ⟨c, i⟩ =
      ⟨c, (localMap H f.hom).indexMap i⟩ := rfl

/-- No algebra data are replaced: these are exactly the original bounded pullbacks. -/
theorem pointContinuousQuotientFunctor_map_pullback
    {X Y : PointContinuousNonemptyAtlasAction.{u, max z v, max z w, z} K H}
    (f : X ⟶ Y) (c : G ⧸ H) (i : X.obj.V.nonemptyPresentation.atlas.Index) :
    ((pointContinuousQuotientFunctor H hH).map f).hom.hom.pullback ⟨c, i⟩ =
      f.hom.hom.pullback i.val :=
  quotientMap_pullback H hH f.hom c i

/-- The subgroup inclusion as an actual continuous monoid homomorphism. -/
def continuousSubtype : H →ₜ* G :=
  { H.subtype with continuous_toFun := continuous_subtype_val }

/-- Restrict the precise jointly continuous supplied action to the subgroup. -/
def pointContinuousRestriction :
    PointContinuousNonemptyAtlasAction.{u, max z v, max z w, z} K G ⥤
      PointContinuousNonemptyAtlasAction.{u, max z v, max z w, z} K H :=
  PointContinuousNonemptyAtlasAction.restrict (continuousSubtype H)

omit [IsTopologicalGroup G] in
theorem pointContinuousRestriction_obj
    (Y : PointContinuousNonemptyAtlasAction.{u, max z v, max z w, z} K G) :
    ((pointContinuousRestriction H).obj Y).obj =
      (Action.res (AffinoidAtlasPresentation.{u, max z v, max z w} K) H.subtype).obj Y.obj :=
  rfl

omit [IsTopologicalGroup G] in
theorem pointContinuousRestriction_toNonempty :
    pointContinuousRestriction (K := K) H ⋙
        PointContinuousNonemptyAtlasAction.toNonempty =
      PointContinuousNonemptyAtlasAction.toNonempty ⋙
        NonemptyAtlasAction.restrict H.subtype := rfl

end Langlands.Analytic.AtlasInducedAction
