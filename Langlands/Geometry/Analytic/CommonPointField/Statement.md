# A common algebraically closed field for analytic points

`CommonAlgebraicallyClosedPointFieldStatement` is a geometric prerequisite for
the analytic étale cohomology comparison. This module states the prerequisite
and contains no existence proof.

For every complete ultrametric normed field `K : Type u` and every analytic
space `X : LocalizedCategory.{u, v, v} (K := K)`, it asserts the existence of a
field `L : Type (max u (v + 1) uL)` with a normed field structure, an
ultrametric norm, completeness, algebraic closedness, and a `NormedAlgebra K L`
structure, such that the natural projection
`(localizedFieldPointProjection L).app X` is surjective.
The existentially bound structures are the structures used by that projection.
The parameter `uL` allows the witness to lie in any of these larger universes.
There is no nontrivial valuation or characteristic assumption, and `X` need
not be compact or Hausdorff.

The projection is the published projection from `L`-valued points to the
underlying points of `X`, with a universe lift on its codomain. Thus
surjectivity says that every underlying point has an `L`-valued lift.
On a presentation, such a lift includes compatible evaluations in every
affinoid chart containing the point, with norms equal to the chart seminorm.
The statement requires a single `L` for all points of `X`; a separate field
for each point does not suffice.

The provenance is derived. Berkovich, *Étale cohomology for non-Archimedean
analytic spaces* (1993), registered as `berkovich-1993-etale-cohomology`,
SHA256 `06b42aca1c8f237e607d2cf1f15a41fdc9718324a4dc9fd5bce66574254bb91c`,
§1.4, printed p.30 / PDF p.27, associates a completed residue field
`H(x)` to each analytic point, with compatible canonical bounded characters
from affinoid domains containing that point. This is the source behind the
published compatible-family definition of `FieldPoint`.
The common field and the stated universe bound are additional derived
requirements, rather than a quotation of that passage.

A proof must construct the chart-compatible realizations, embed their fields
into one common normed extension, and obtain a complete algebraically closed
ultrametric extension while controlling the universe. None of these steps
is supplied by this statement module. Pairwise field amalgamation alone
does not perform the common-field construction for all points.

The chosen field universe is intended for the existing cohomology interface:
substituting `max u (v + 1) uL` for the auxiliary field universe leaves
`max u (v + 1) uL` as the coefficient and module universe. The statement
does not assert the étale point axioms; those are the separate
`EtaleSite.GeometricPointStatement`. It also does not prove acyclicity or
either analytic comparison theorem.
