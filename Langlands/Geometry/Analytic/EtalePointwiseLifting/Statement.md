# Pointwise lifting squares in the analytic étale site

This module states
`Langlands.Analytic.SaturatedAtlasPresentation.EtalePointwiseLiftingStatement`.
It isolates a geometric prerequisite for the covering-points input to the
compact analytic étale cohomology comparison. The proposition has no proof
here; the two subsequent theorems identify its categorical meaning and prove
its conditional covering-points consequence.

## Exact statement

Let `K : Type u` be any complete ultrametric normed field and
`X : LocalizedCategory.{u, v, v} (K := K)` any analytic base. Take any
cospan `f : U ⟶ W`, `g : V ⟶ W` in the actual category `EtaleSite X`,
and ordinary underlying points `x` of `U` and `y` of `V` with equal images
in `W`. The statement requests an object `T : EtaleSite X`, morphisms
`p : T ⟶ U` and `q : T ⟶ V`, and an ordinary point `t` of `T` such that

- `p ≫ f = q ≫ g` as morphisms of `EtaleSite X`;
- the underlying point map of `p` sends `t` to `x`;
- the underlying point map of `q` sends `t` to `y`.

The point maps are exactly `EtaleSite.points X`. In particular, the
conclusion requires a genuine étale object over `X`, with both morphisms
over `X`. Equality only of underlying point maps is insufficient for the
commuting equation.

The coefficient-field universe `u` and the space and index universe `v`
are independent. No Hausdorff hypothesis is imposed on `X`, `U`, `V`,
or `W`. There is no compactness assumption, group action, supplied
base-change theorem, or assumption that a categorical pullback exists.
The lifting square and its object may depend on the two prescribed
points. The statement does not assert uniqueness or a universal property.

## Implemented conditional reduction

`etalePointwiseLiftingStatement_iff` identifies the proposition, by
definitional equality, with
`∀ X, PointwiseCovering.HasPointwiseLiftingSquares (EtaleSite.points X)`.
The generic predicate quantifies over precisely the same cospans, points,
objects, morphisms, and commuting equations.

`jointlySurjective_of_mem_etaleTopology_of_pointwiseLifting` assumes the
statement for `K` and proves that every covering sieve on every object
of `EtaleSite X` is jointly surjective on ordinary underlying points.
Its proof applies
`PointwiseCovering.isJointlySurjective_of_mem_toGrothendieck` to `h X`.
This application uses the existing definition
`etaleTopology X = (Types.jointlySurjectivePrecoverage.comap
(EtaleSite.points X)).toGrothendieck`.
The generic result handles the pullback and transitivity saturation of
the precoverage, so the conclusion concerns all covering sieves.

This gives exactly the covering-points conclusion needed by the compact
finite-subcover argument once the geometric lifting statement is proved.
It does not assume the covering-points conclusion or claim to prove it
unconditionally.

## Provenance and remaining geometry

This is an internal prerequisite statement specialized from
`Langlands.CategoryTheory.PointwiseCovering.HasPointwiseLiftingSquares`
to the Library's actual analytic étale site. It is not a transcription of
a separately numbered literature assertion. The explicit specialization
and the implemented implication above explain why this prerequisite is
relevant and what a future proof must supply.

The existing `FibreProduct.exists_point` in
`Langlands.Geometry.Analytic.FibreProductPoints` lifts compatible points
of compatible strong maps to the actual glued fibre-product chart-system
space, assuming both source atlases contain all local domains. That result
has independent universes and no Hausdorff hypothesis. Its specialization
`SaturatedAtlasPresentation.exists_fibreProduct_point` concerns the
existing analytic fibre product of Hausdorff saturated presentations with
all universes equal to the coefficient-field universe. These are partial
geometric inputs, not instances of the present statement.

A proof here must still provide the étale lifting object and its maps
for arbitrary localized site arrows, prove that its structure map to
`X` is étale, and establish the commuting equation in the site. It must
also retain the full non-Hausdorff and independent-universe scope.
`EtaleBaseChangeStatement` concerns Hausdorff same-universe strong maps
only; even a proof of that proposition would leave these assembly
obligations. No categorical fibre-product universal property is required
by the present target.

Neither the statement nor its conditional reduction proves étale
openness, finite subcovers from compactness, higher acyclicity, or
`AnalyticEtaleGlobalComparisonStatement`.
