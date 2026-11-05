# Finite coordinate tests for actual affine integral points

This internal construction concerns an actual affine scheme `X` over
`Spec R`, where `R` is any commutative ring in an arbitrary universe `u`.
The coordinate ring is the published `AffineCoordinateRing R X`, namely the
global sections of `X` with their specified `R`-algebra structure. Points are
the existing relative scheme morphisms `RingPoint R X L`.

For any commutative `R`-algebra `L : Type u` and any `R`-subalgebra `T` of `L`,
`mem_range_changeRing_subalgebra_iff` says that an `L`-point is obtained by
coefficient change from an actual `T`-point if and only if every global
function evaluates in `T`. The forward direction uses the published
coefficient-change formula for `affineSchemePointEquiv`. The reverse
direction restricts the point's coordinate algebra homomorphism to `T`,
then applies the inverse of that equivalence. Its coefficient change
recovers the original point by injectivity of the same equivalence.

`mem_range_changeRing_subalgebra_iff_of_adjoin_eq_top` allows any specified
set of algebra generators in place of all functions. The inverse image of
`T` under the evaluation homomorphism is an `R`-subalgebra. If it contains
the generators, it contains their algebraic closure, hence the whole
coordinate ring.

If `X.hom` is locally of finite type, the existing affine-coordinate
finite-type instance supplies a finite generating set.
`exists_finset_integralPointCriterion` gives one finite test set before
the value algebra, subalgebra and point are chosen.
`integralPointTestSet` fixes such a set by classical choice, and
`mem_range_changeRing_subalgebra_iff_testSet` states its uniform extension
criterion. These declarations require the locally finite-type hypothesis
only for the finite choice; the preceding all-function and generating-set
criteria do not require it.

`eventually_range_changeRing_of_eventually_evaluation` applies the criterion
to a family of value algebras, their subalgebras and sets of points, indexed
by any `ι : Type w` with any filter. It assumes that for each global function,
eventually every point in the corresponding set evaluates into the
corresponding subalgebra. The eventual set may depend on the function, but
is uniform over the point set. The proof intersects the finitely many
eventual assertions for the test functions using `eventually_all_finite`.
It then applies the extension criterion to every point at each remaining
index. The conclusion is eventual inclusion of the whole point set in the
range of coefficient change.

The provenance is internal: the construction is derived from the Library's
global-section point equivalence, its coefficient naturality and its
finite-type coordinate instance, together with codomain restriction of
algebra maps and closure under algebra generation. No external theorem is
asserted here. Application to the arithmetic Iwasawa family still requires
identifying the relevant actual model points and proving the assumed
functionwise integrality for that family.
