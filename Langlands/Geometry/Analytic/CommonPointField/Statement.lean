import Langlands.Geometry.Analytic.FieldValuedPoints

/-!
# A common algebraically closed field for the points of an analytic space

This is a geometric prerequisite statement. It asserts existence of one field
realizing every underlying point, without assuming the étale point axioms.
-/

universe u v uL

namespace Langlands.Analytic.SaturatedAtlasPresentation

/-- Every analytic space admits a complete algebraically closed ultrametric extension
field realizing all its underlying points. The field universe is chosen to preserve
the coefficient universe `max u (v + 1) uL` used by analytic étale cohomology. -/
def CommonAlgebraicallyClosedPointFieldStatement : Prop :=
  ∀ (K : Type u) [NormedField K] [IsUltrametricDist K] [CompleteSpace K]
    (X : LocalizedCategory.{u, v, v} (K := K)),
    ∃ (L : Type (max u (v + 1) uL)) (_ : NormedField L) (_ : IsUltrametricDist L)
      (_ : CompleteSpace L) (_ : IsAlgClosed L) (_ : NormedAlgebra K L),
      Function.Surjective ((localizedFieldPointProjection L).app X)

end Langlands.Analytic.SaturatedAtlasPresentation
