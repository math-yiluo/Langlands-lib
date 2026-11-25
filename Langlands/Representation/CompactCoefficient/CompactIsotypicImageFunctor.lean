import Langlands.Representation.CompactCoefficient.CompactProjectionDistributionConstruction
import Langlands.Representation.Category.Subquotients
import Mathlib.CategoryTheory.Center.Basic

/-! # The image functor of a compact isotypic projector -/

noncomputable section

set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory MeasureTheory

universe u v

namespace Langlands.Renard.CompactRepresentation.ProjectionDistribution

variable {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [LocallyCompactSpace G] [T2Space G] [TotallyDisconnectedSpace G]
  [MeasurableSpace G] [BorelSpace G] (μ : Measure G) [μ.IsHaarMeasure]
  (D : IrreducibleCompactCoefficientRep.{u, v} G)

/-- Renard IV.1.5, Remark 3: the isotypic projector is a natural endomorphism
of the identity of the smooth representation category. -/
def projectorCenter : CatCenter (SmoothRep.{0, u, v} ℂ G) where
  asHom.app A := SmoothRep.ofHom (projector μ D A)
  asHom.naturality A B f := by
    ext x
    exact (projector_natural μ D (SmoothRep.hom f) x).symm

/-- Renard (IV.1.5.1): the actual smooth image of the compact isotypic projector,
with morphisms restricted by its naturality. -/
def projectorImageFunctor : SmoothRep.{0, u, v} ℂ G ⥤ SmoothRep.{0, u, v} ℂ G where
  obj A := SmoothRep.subrepresentation A (projector μ D A).range
  map {A B} f := SmoothRep.ofHom {
    toLinearMap :=
      ((SmoothRep.hom f).toLinearMap.comp (projector μ D A).range.toSubmodule.subtype).codRestrict
        (projector μ D B).range.toSubmodule (by
          rintro ⟨_, x, rfl⟩
          exact ⟨SmoothRep.hom f x, (projector_natural μ D (SmoothRep.hom f) x).symm⟩)
    isIntertwining' g := by
      ext x
      exact Subtype.ext (Representation.IntertwiningMap.isIntertwining _ _ (SmoothRep.hom f) g x.val) }
  map_id _ := by ext x; rfl
  map_comp _ _ := by ext x; rfl

/-- Inclusion of the actual image into the original representation. -/
def projectorImageInclusion : projectorImageFunctor μ D ⟶ 𝟭 _ where
  app A := SmoothRep.subtype A (projector μ D A).range
  naturality _ _ _ := by ext x; rfl

/-- The projector with codomain restricted to its image. -/
def projectorImageProjection : 𝟭 _ ⟶ projectorImageFunctor μ D where
  app A := SmoothRep.ofHom {
    toLinearMap := (projector μ D A).toLinearMap.rangeRestrict
    isIntertwining' g := by
      ext x
      exact Subtype.ext (Representation.IntertwiningMap.isIntertwining _ _ (projector μ D A) g x) }
  naturality _ _ f := by
    ext x
    exact Subtype.ext (projector_natural μ D (SmoothRep.hom f) x).symm

theorem projectorImageProjection_comp_inclusion :
    projectorImageProjection μ D ≫ projectorImageInclusion μ D = (projectorCenter μ D).asHom := rfl

theorem projectorImageInclusion_comp_projection :
    projectorImageInclusion μ D ≫ projectorImageProjection μ D = 𝟙 (projectorImageFunctor μ D) := by
  apply NatTrans.ext
  funext A
  ext x
  apply Subtype.ext
  change projector μ D A x.val = x.val
  obtain ⟨y, hy⟩ := x.property
  rw [← hy]
  exact LinearMap.congr_fun
    (CompactCoefficientClass.isotypicProjectorOfIsCompl_idempotent
      (CompactCoefficientClass.ofRep D)
      (CompactSplitting.isCompl_isotypicSubrepresentation_annihilatorSubrepresentation
        μ compactOpenCofinal (CompactCoefficientClass.ofRep D) A)) y

end Langlands.Renard.CompactRepresentation.ProjectionDistribution
