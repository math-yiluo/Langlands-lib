# Positive forms from compact coefficient norms modulo the center

Worker 1668, with Worker 1678, supplies this derived construction for the
unitarity implication of Renard VI.2.1 and IV.3.2. Worker 1678 proposed the
direct compact-coefficient integration route; Worker 1668 implemented this
wrapper and its nonarchimedean specialization. It composes published proofs
and the actual Haar measure construction; it makes no additional assertion
about algebraic groups or about compactness of supercuspidal coefficients.

`Langlands.UnitaryCentralCharacter.compactCoefficientPositiveForm.{uG,uV}`
constructs an `InvariantPositiveForm ρ` on the original algebraic carrier of an
irreducible smooth complex representation. The group is an arbitrary locally
compact Hausdorff topological group. Its universe `uG` and the carrier universe
`uV` are independent. The inputs are a unitary character acting on the full
abstract center, compact support of every smooth-dual coefficient norm on the
actual quotient `G ⧸ Subgroup.center G`, and cofinality of compact open subgroups.
There is no topology or dimension restriction on the representation carrier.

The full center is closed by `Set.isClosed_centralizer`; its group quotient
is therefore Hausdorff and locally compact. We install the Borel measurable
space on this quotient and take the inverse of its actual left Haar measure,
`(Measure.haar : Measure Q).inv`. Inversion converts left invariance into
right invariance, preserves finiteness on compact sets, and preserves positivity
on nonempty open sets. These properties suffice for the construction.

The published
`exists_nonzero_smoothDual_of_irreducible_compact_cofinal`
from `Langlands.Representation.Unitary.SquareIntegrableProof` supplies a nonzero
smooth functional `ℓ`. For every vector `v`, the published
`UnitaryCentralCharacter.continuous_coefficientNorm` and the supplied compact
support give `MemLp (c.coefficientNorm ℓ.1 v) 2` for the inverse Haar measure,
by Mathlib's `Continuous.memLp_of_hasCompactSupport`.

The construction then applies the published
`UnitaryCentralCharacter.coefficientProductForm`. Its inner product is the
integral of the conjugate-first coefficient product against that right
invariant measure. The published proof establishes sesquilinearity and
invariance, nonnegativity of the diagonal, and definiteness: a zero diagonal
integral makes the continuous coefficient vanish everywhere, and
irreducibility with `ℓ ≠ 0` forces the vector to be zero.

`isUnitarizable_of_compact_coefficientNorm` records the nonempty conclusion.
`isUnitarizable_of_compact_coefficientNorm_of_nonarchimedean` obtains the
cofinality input from the published `compactOpenSubgroupBasis`, using local
compactness and `NonarchimedeanGroup G`.

This is an internal generalization of the integration argument already
implemented in `SquareIntegrableProof` and of the inverse-Haar assembly in
`Aubert.General.RationalCompactRestrictionUnitarity`. Unlike the separate
predicate `IsSquareIntegrableModCenter`, the construction does not ask for
admissibility. Compact support makes the coefficient norms square integrable
for right Haar directly, so it also requires no unimodularity or second
countability premise. These are precise features of this derived construction.

For source orientation, Renard, *Représentations des groupes réductifs
p-adiques*, version of 9 July 2026, IV.3.1–IV.3.2, printed pp.99–100 / PDF
pp.105–106, constructs invariant forms from square-integrable coefficients.
That passage works with a unimodular group and also proves admissibility and
semisimplicity in its stated scope. This unit claims only the construction
described above and uses a different, previously formalized irreducibility
argument for definiteness. The source is registered as
`renard-2026-representations-groupes-reductifs-padiques`, SHA256
`7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`;
Worker 1668 read both cited PDF pages.
