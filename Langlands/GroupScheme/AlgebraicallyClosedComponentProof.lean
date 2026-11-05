import Langlands.GroupScheme.AlgebraicallyClosedComponentStatements

/-! # Rational representatives of actual scheme components -/

universe u

open CategoryTheory CategoryTheory.MonoidalCategory AlgebraicGeometry

namespace Langlands.GroupScheme.IdentityComponent

variable {k : Type u} [Field k] [IsAlgClosed k]
    (H : GroupScheme (Spec (CommRingCat.of k)))

/-- Every connected component of a locally finite type group scheme over an
algebraically closed field contains a rational section. -/
theorem pointComponent_surjective_of_isAlgClosed [LocallyOfFiniteType H.X.hom] :
    Function.Surjective (pointComponent H) := by
  let : JacobsonSpace H.X.left := LocallyOfFiniteType.jacobsonSpace H.X.hom
  intro c
  obtain ⟨p, rfl⟩ := _root_.ConnectedComponents.surjective_coe c
  obtain ⟨q, hqp, hq⟩ := nonempty_inter_closedPoints
    (show (connectedComponent p).Nonempty from ⟨p, mem_connectedComponent⟩)
    isClosed_connectedComponent.isLocallyClosed
  change IsClosed ({q} : Set H.X.left) at hq
  refine ⟨Over.homMk (pointOfClosedPoint H.X.hom q hq)
    (pointOfClosedPoint_comp H.X.hom q hq), ?_⟩
  change _root_.ConnectedComponents.mk
    (pointOfClosedPoint H.X.hom q hq (basePoint k)) =
      _root_.ConnectedComponents.mk p
  rw [pointOfClosedPoint_apply]
  exact _root_.ConnectedComponents.coe_eq_coe'.mpr hqp

/-- The ordinary rational-point quotient accounts for every actual scheme
component of a smooth affine group over an algebraically closed field. -/
theorem rationalComponentEmbedding_bijective_of_isAlgClosed
    [Smooth H.X.hom] [IsAffineHom H.X.hom] :
    Function.Bijective (rationalComponentEmbedding H) := by
  refine ⟨(rationalComponentEmbedding H).injective, ?_⟩
  intro c
  obtain ⟨x, hx⟩ := pointComponent_surjective_of_isAlgClosed H c
  exact ⟨rationalComponentProjection H x,
    (rationalComponentEmbedding_projection H x).trans hx⟩

/-- Rational sections represent all actual components over algebraically closed
fields, and the published rational quotient embedding is bijective. -/
theorem algebraicallyClosedComponentComparison :
    AlgebraicallyClosedComponentComparisonStatement.{u} := by
  constructor
  · intro k _ _ H _
    exact pointComponent_surjective_of_isAlgClosed H
  · intro k _ _ H _ _
    exact rationalComponentEmbedding_bijective_of_isAlgClosed H

end Langlands.GroupScheme.IdentityComponent
