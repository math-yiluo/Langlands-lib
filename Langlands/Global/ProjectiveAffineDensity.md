# Standard affine charts of actual projective points

This is derived geometric infrastructure for Brian Conrad, *Weil and
Grothendieck approaches to adelic points* (December 31, 2011), printed page 10,
Example 4.3. Conrad proves density of global rational projective points using
matrix approximation and projective changes of coordinates. The present
construction supports a different route: each standard affine chart is dense
in the local projective point space. Arithmetic coefficient approximation and
the comparison with actual adelic projective points are separate obligations.

## Construction and naturality

For any commutative base ring `R`, dimension `n : ℕ`, and index
`j : Fin (n + 1)`, the construction reuses the published
polynomial-algebra equivalence with the actual homogeneous localization chart
of polynomial Proj. Its generator lemma identifies the variables with the
ratios of homogeneous coordinates by coordinate `j`.

For any commutative `R`-algebra `A`, `projectiveAffinePoint R A n j a`
evaluates the polynomial coordinates at `a` and then composes with the
published standard relative open immersion. The target is the actual
relative scheme-point set `RingPoint R (projectivePointScheme R n) A`.
`projectiveAffinePoint_changeRing` proves naturality for every coefficient
`R`-algebra homomorphism. It follows from contravariance of Spec and uniqueness
of a polynomial algebra homomorphism on its variables.

## Point topology and coverage

`isOpenEmbedding_projectiveAffinePoint` uses the product topology on the
coordinate function space and the independently constructed
`schemePointTopology` on the projective points. Its assumptions on `A` are a
commutative local ring and a topology with continuous ring operations. It also
assumes `IsOpenUnits A`: the units form an open subset of `A`, and inversion is
continuous for the subspace topology on the units (equivalently, `Units.val` is
an open embedding for Mathlib’s canonical unit-group topology). The proof composes the inverse polynomial-point homeomorphism with the
open embedding on points induced by the standard open immersion. It does not
define the projective point topology by this chart map.

For a field `A` over any commutative `R`,
`exists_projectiveAffinePoint` proves that every actual relative projective
point is represented in some standard chart. The homogeneous coordinate
opens cover the projective scheme. The image of the closed point of
`Spec A` therefore lies in one of them; the local-spectrum criterion makes
the full morphism factor through this open. The lifted morphism retains its
map to `Spec R`. The spectrum/algebra-point equivalence and the polynomial
chart equivalence recover its coordinate values, and uniqueness of polynomial
evaluation reconstructs the original point.

## Coordinates, switching charts, and density

`projectiveAffineCoordinates` inserts `1` at the selected homogeneous
coordinate. `projectiveAffineChartEvaluation` is the corresponding algebra
map on the homogeneous localization. Its ratio lemma evaluates each
homogeneous coordinate ratio to the inserted coordinate vector.
`projectiveAffinePoint_left` identifies the underlying scheme morphism with
Spec of this evaluation followed by the actual Proj chart inclusion.

If the inserted vector has nonzero coordinate `j`, then
`projectiveAffinePoint_changeChart` identifies its point with the chart `j`
point obtained by dividing all other coordinates by that coordinate. The
proof applies the published comparison of chart morphisms after explicitly
verifying their homogeneous ratio identities.

For a field `A` with continuous ring operations, `IsOpenUnits A` (open units
and continuous inversion for their subspace topology), and `PerfectSpace A`
(no isolated points), `denseRange_projectiveAffinePoint`
proves that each selected chart map has dense range in the independent
projective point topology. In any other chart, the coordinate vectors with
all entries nonzero form a dense subset: the complement of a singleton is
dense, and products preserve density. Chart switching puts its image inside
the selected chart. Continuity then puts every point of the other chart in
the closure of the selected chart. Chart coverage completes the proof.

All types use an arbitrary common universe. Every dimension is allowed,
including `n = 0`; its empty tuple of affine coordinates causes no exception.
The module asserts no arithmetic approximation theorem, adelic rational-point
density, nonclosedness, or nondiscreteness.
