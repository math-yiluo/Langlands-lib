# Failure of embedding for adelic punctured-line points

`AdelicPunctureEmbeddingStatement` states the failure of embedding discussed in
Brian Conrad, *Weil and Grothendieck approaches to adelic points* (2011),
printed pp.3–4, opening of section 3, and printed p.11. The registered source is
`conrad-2011-weil-grothendieck-adelic-points`, SHA256
`fe4a9193aff4ef575665b40971f3da32f850a74d87b3f2d0fa28bba26b9cbabb`.
For an open affine `U` in an affine `X`, Conrad says that `U(R) → X(R)` "may
even fail to be a topological embedding". His example takes `X` to be the affine
line and `U` the complement of the origin, so that the map is the inclusion
`R× → R`. Here `R×` carries the topology of the hyperbola `xy = 1`, in which
units are close when both their values and their inverses are close. He then
notes that adele rings show "the unit group of a topological ring need not be a
topological group with respect to the induced topology from the ring". Since the
hyperbola topology makes `R×` a topological group, the inclusion `R× → R` cannot
be a topological embedding in such examples. On printed p.11, in the paragraph
before Theorem 4.5, Conrad repeats the example over a global field `F`. The
open immersion of the multiplicative group into the affine line over `F` induces
the inclusion `A_F× → A_F`, "which is not even a topological embedding and does
not have open image".

`AffineLinePunctureEmbeddingObstruction S` packages three conclusions for a
commutative ring `S` with its given topology:

1. The unit group `Sˣ` with the topology induced by `Units.val : Sˣ → S` is not
   a topological group. When multiplication on `S` is continuous, so is
   multiplication for this topology, since it is the restriction of ring
   multiplication. The clause then says that inversion is not continuous for the
   subspace topology.
2. `Units.val : Sˣ → S` is not a topological embedding when `Sˣ` carries Mathlib's
   existing units topology. That topology is induced by the value and the
   inverse value, which is Conrad's hyperbola topology.
3. For every commutative base ring `R` in the same universe, with any algebra
   structure on `S`, the actual point map is not a topological embedding. This is
   postcomposition with the open immersion `affineLinePunctureι R` from the
   punctured affine line into the affine line over `R`. Both point spaces carry
   the existing global-section evaluation topology on actual relative `S`-points.
   The base `R = S` with its identity algebra is Conrad's case on p.3 of schemes
   over the topological ring itself. A global field as base, with its diagonal
   algebra structure on its adeles, is his case on p.11. All other bases are
   included in the same proposition.

The general definition only names this proposition. It fails, for instance, for
the real numbers. It assumes none of its conclusions.

`NumberFieldPunctureEmbeddingStatement` asserts the three conclusions for the
original full adelic ring `Adeles K` of every number field `K`, including its
archimedean factors. `CurvePlacePunctureEmbeddingStatement` asserts them for the
actual curve-place adelic ring `CurvePlaceAdeleRing k F` of every specified
finite extension `F` of `RatFunc k`. Here `k` is an arbitrary constant field and
the rational-function action and compatible scalar tower are retained. No
finiteness or perfectness of `k` and no separability of `F` are assumed. Both
clauses use the existing arithmetic restricted-product topologies. Neither
carrier is replaced by an abstract place system. The combined target is the
conjunction of the two clauses, in an arbitrary common universe.

Provenance: Conrad states the failure of embedding for adele rings in prose,
without a proof and, on p.3, without fixing a global field. The arithmetic
carriers, the use of both characteristics, and the quantification over all base
rings are this formalization's precise reading of these remarks. Clause 1 is his statement about
the unit group with the induced topology. Clause 2 is the inclusion `R× → R`
with the hyperbola topology. Clause 3 is the map `U(R) → X(R)` on actual scheme
points, over the topological ring itself (p.3) or over the global field
(p.11). The comparison of actual punctured-line points with the units topology
is `affineLinePunctureUnitHomeomorph` in `AffineLinePunctureUnits`. The
affine-line coordinate homeomorphism is `affineLinePointHomeomorph` in
`AffineLineOrigin`. Openness of the image is the separate
`AdelicUnitLocusStatement`. The `n`-th power counterexample on p.11 is not
part of this statement.
