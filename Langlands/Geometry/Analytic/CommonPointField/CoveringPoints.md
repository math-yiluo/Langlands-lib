# Covering points detected by field-valued site points

Worker 284. This internal construction derives
`EtaleCoveringPointsStatement` from the explicit common-field existence and
geometric-point propositions. Neither input is proved here.

The base field has the complete ultrametric normed field instances, with
independent field and space universes `u` and `v`. The common-field
proposition is used at universes `u`, `v`, `uL`, and the geometric-point
proposition is used at `u`, `v`, `max u (v + 1) uL`. There is no compactness,
Hausdorffness, nontrivial valuation or characteristic premise.

For a covering sieve on an étale object `U` and an ordinary point of `U`, the
common-field premise is applied to `U.left`. Its surjective projection gives
a field-valued point `p` lifting the ordinary point. Map `p` along the
structure morphism to obtain a field-valued point of the base. The second
point axiom lifts the fibre element `p` through an arrow in the sieve.
Projection naturality identifies the image of the resulting ordinary point
with the original point.

`coveringPoints_of_commonPointFields` packages the argument as the exact
covering-points proposition. Only the joint-surjectivity part of the point
axioms is used. The proof concerns arbitrary covering sieves in the actual
`etaleTopology`, without reducing them to the generating precoverage or
assuming an additional pointwise-lifting square.

`coveringPointLiftOfCommonPointFields` uses classical choice to return the
constructed data for a specified covering sieve and ordinary point. Its
dependent result contains an étale object `V`, an arrow `f : V ⟶ U`, and an
ordinary point of `V`, together with proofs that `f` belongs to the sieve and
maps this point to the specified point of `U`.

The field chosen for this argument can depend on the étale object. The final
comparison separately chooses a common field for the base space when it
applies restricted-injective acyclicity. The enlarged field universe is
`max u (v + 1) uL` in both uses. This is an internal categorical argument
using the published point definitions, rather than a new literature claim.

The construction does not prove either field-valued-point prerequisite,
restricted-injective acyclicity, or an analytic comparison theorem.
