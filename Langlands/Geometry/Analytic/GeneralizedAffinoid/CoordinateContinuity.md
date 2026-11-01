# Continuity from finite coordinates of actual weighted quotients

Authors: Worker 56 (positive-radius extension); Worker 474 and Worker 36
(published strict coordinate-continuity proof and its proof route).

This module adapts the generic coordinate and approximation lemmas of
`StrictTestDomain.RationalSectionContinuityProof` to arbitrary positive-radius
presentations. It constructs a full norm-continuous action from continuity of
only the finitely many coordinate orbits at the group identity. The required
local bound on all section operators is derived from the finite presentation.

## Actual data and norms

The field `K : Type u` is normed and ultrametric. The source `A` and target `B`
are actual `PresentedAffinoidAlgebra K` objects: each is the concrete quotient
of its chosen finite positive-polyradius Tate algebra by a closed ideal,
with the constructed quotient norm. Write `r = A.polyradius`, `q_A =
presentationMap K A`, and `a_i = coordinate K A i`. The imported bound is
`‖a_i‖ ≤ r_i`.

The generic local-continuity declarations take an arbitrary topological
parameter space `T : Type v`, a center `x : T`, and a family of actual bounded
`K`-algebra maps `φ(t) : A → B`. The coordinate continuity hypothesis is
`ContinuousAt (fun t => φ(t)(a_i)) x` for every `i`.
Their center bound is explicitly `‖φ(x)(a_i)‖ ≤ r_i`. Neither a common
operator bound near `x` nor continuity on all sections is supplied.
There is no coefficient-completeness hypothesis in this module.

All declarations are in `Langlands.Analytic.PresentedAffinoidAlgebra`.

## Contraction and one common neighborhood

`norm_map_le_of_coordinates` proves that a single actual bounded map `φ`
is contractive if `‖φ(a_i)‖ ≤ r_i` for every source coordinate.
Compose `φ` with the actual quotient map `q_A`.
The published weighted `map_eq_evaluate` expresses its value on every
Tate series as evaluation at the coordinate images.
`monomialValue_norm_le_weight` supplies the monomial bound with constant
one from the coordinate bounds and `‖(1 : B)‖ ≤ 1`.
The latter is the actual quotient-unit bound `norm_one_le K B`.
Consequently `evaluate_norm_le_bound` gives
`‖φ(q_A(f))‖ ≤ ‖f‖`.

For a quotient element `a` and each `ε > 0`,
`exists_representative_norm_lt` chooses a representative `f` with
`q_A(f) = a` and `‖f‖ < ‖a‖ + ε`.
Passing to arbitrarily small positive `ε` proves `‖φ(a)‖ ≤ ‖a‖`.
This uses the actual quotient infimum and no open-mapping theorem.
The monomial bound includes the empty product when the target is zero;
no target nontriviality or `NormOneClass B` is needed.

`eventually_coordinates_norm_le` treats a finite tuple `c(t,i)` in any
actual target presentation and arbitrary positive radii `s_i`.
If each entry is continuous at `x` and `‖c(x,i)‖ ≤ s_i`, continuity makes
`‖c(t,i)-c(x,i)‖ < s_i` near `x`.
The actual quotient's ultrametric inequality then gives

\[
 \|c(t,i)\|
 \le \max\bigl(\|c(t,i)-c(x,i)\|,\|c(x,i)\|\bigr)\le s_i.
\]

Finite intersection combines the neighborhoods for all entries.
`eventually_contractive_of_coordinates` applies this result with
`s = A.polyradius`, then applies the preceding contraction criterion.
Its conclusion is one neighborhood on which
`∀ a : A, ‖φ(t)(a)‖ ≤ ‖a‖`.
The quantifier over every section is inside this common neighborhood.
For an empty coordinate type the finite conjunction is vacuous, and the
same evaluation proof still gives the conclusion.

## Finite approximation and arbitrary section continuity

`continuousAt_map_monomial` applies the published weighted monomial map
formula. A mapped coefficient monomial is a fixed scalar times a finite
product of powers of coordinate images, so it is continuous at `x`.
`continuousAt_map_partial_sum` applies finite-sum continuity and preservation
of sums by the actual quotient and algebra maps.

`exists_partial_sum_approx` approximates each actual quotient element `b`
by a quotient image of a finite coefficient-monomial sum.
Choose a genuine Tate representative using surjectivity of `q_A`.
The published unconditional monomial expansion converges to that
representative in the weighted Tate norm.
Contractivity of `q_A` passes the approximation to the actual quotient norm.
Completeness of `K`, `A` or `B` is not used: the imported expansion already
converges to the given series.

`continuousAt_map_of_coordinates` combines these results. For `ε > 0`,
choose such a finite-sum image `q` with `‖b-q‖ < ε/3`.
The derived common local contraction bounds
`dist(φ(t)(b),φ(t)(q))` by `‖b-q‖`.
The contraction criterion at the center bounds
`dist(φ(x)(q),φ(x)(b))` by the same number.
Continuity of the finite sum makes
`dist(φ(t)(q),φ(x)(q)) < ε/3` near `x`.
The triangle inequality makes the distance between the two images of `b`
less than `ε`, proving continuity at `x`.

## From identity coordinates to the full action

`continuous_map_of_continuousAt_one` takes a topological group `G : Type v`
and a multiplicative family of actual bounded endomorphisms `φ(g)` of `A`,
with every section orbit continuous at `1`.
At `g₀`, continuous group translation sends `g` to `g₀⁻¹g` tending to `1`.
Compose the orbit's continuity there with the fixed continuous bounded map
`φ(g₀)`. Multiplicativity identifies
`φ(g₀)(φ(g₀⁻¹g)(a))` with `φ(g)(a)` and identifies the center value.
Thus every orbit is continuous everywhere.

`normContinuousActionOfCoordinates A σ hc` starts with a homomorphism
`σ : G →* Aut A` and continuity only at `1` of the finitely many functions
`g ↦ (σ g).hom.toAlgHom a_i`.
At `1` the bounded map is the identity, so its coordinate bounds follow
from `norm_coordinate_le K A`.
`continuousAt_map_of_coordinates` gives every section orbit's continuity
at `1`, and the translation theorem gives continuity everywhere.
The construction then uses `NormContinuousAction.ofAut` to produce an
object of the published category of norm-continuous actions on actual
presented quotients.
`normContinuousActionOfCoordinates_actionAut` proves that its bounded
automorphism homomorphism is exactly the supplied `σ`.
No action, topology, norm, coordinate or quotient presentation is replaced.

## Provenance and scope

Worker 56 implements the weighted extension of the generic lemmas in
`Langlands.Geometry.Analytic.StrictTestDomain.RationalSectionContinuityProof`,
whose Lean proof is by Worker 474 and whose proof route was supplied by
Worker 36. Both are credited as coauthors of this adaptation.
The radius-specific neighborhood thresholds replace the strict proof's
unit thresholds. The zero-safe weighted monomial theorem replaces the
strict proof's nonzero-target normalization step. The constructor from
identity-coordinate orbits is a derived application of the resulting
local continuity and translation lemmas.

The original geometric conventions are in Vladimir Berkovich,
*Non-archimedean analytic spaces* (Trieste lectures, 2009), registered as
`berkovich-2009-trieste-analytic-spaces`, PDF SHA256
`8cfe4f6f35d5e717ac67c5c8f5ef9ff9185f460bbe5f9a10aeacd84cddeeb2ca`.
Example 1.2.2(v), printed/PDF p.4, gives the arbitrary positive-radius
Tate norm. The quotient-norm discussion and Definition 2.1.2 on p.7
give the affinoid presentation setting; Definition 2.1.11 on p.8 uses
bounded homomorphisms for the opposite category of affinoid spaces.
These pages were read directly.
The source's analytic setting uses complete coefficient fields.
The internal criteria proved here apply to the Library's actual normed
quotients without completeness, because their implemented weighted
evaluation, monomial expansion, quotient estimates and ultrametric
arguments do not need it. These continuity criteria are internal
derivations, not quoted theorems of those source passages.

The field, parameter or group, and auxiliary finite tuple universes are
independent. The valuation may be trivial and the chosen closed ideals
arbitrary. No proper-ideal, reducedness, nonzero-algebra or positive-arity
assumption appears. The target may be zero and both arities may be zero.
All source radii are arbitrary positive real numbers, with no
value-group condition or relation to the target's presentation radii.

This module constructs continuity criteria on actual presented algebras.
It does not construct local rational section maps, prove locus-stabilizer
openness, compare quotient and spectral norms, identify an analytic
automorphism topology, or construct an analytic or equivariant etale site.
