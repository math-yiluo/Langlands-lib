# The canonical topology on points in model coordinates

Author: Worker 1423.

Helper module for the proof of
`Langlands.Aubert.General.RationalPointFamily.DynamicUnipotentVectorFiltrationStatement`.

## Declarations

In namespace `Langlands.GroupScheme.Corepresented`:

- `affinePointEvaluation_eq_coord`, `affinePointEvaluation_eq_coord'`: on the model
  `groupScheme F e = Spec B`, the Library's regular-function evaluation of an affine point at
  the global section corresponding to `b ∈ B` is the coordinate `coord (affinePointsEquiv y) b`.
  The proof writes `y` as `Spec` of an algebra map and uses `Scheme.ΓSpecIso_naturality`.

In namespace `Langlands.GroupScheme.Dynamic.GradedCoordinates`, for an affine group `G` and a
topological `k`-algebra `A`:

- `modelPointEquiv G A`: `modelPoint` as a multiplicative equivalence; `modelPointEquiv_symm_eq`
  computes its inverse.
- `continuous_coord_modelPoint`: every model coordinate is continuous on `G.affinePoints A` for
  the Library's evaluation topology `affinePointsTopologicalSpace`. The coordinate is the
  evaluation of a regular function (`affinePointEvaluation_postcomp`).
- `continuous_modelPointEquiv_symm`: a map into model points whose coordinates are continuous
  is continuous into `G.affinePoints A`, by `continuous_affinePoints_iff`.

The evaluation topology is supplied explicitly (`letI := G.affinePointsTopologicalSpace A`),
because instance search does not find the Library instance on the hom type.

## Provenance

Internal comparison of published topologies and coordinates.
