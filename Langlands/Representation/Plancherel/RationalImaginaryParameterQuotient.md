# Actual period discreteness and the compact imaginary quotient

`rationalImaginaryParameterQuotient` proves all nine clauses of
`RationalImaginaryParameterQuotientStatement`. Worker 6 authored the
original proof; Worker 1444 verified it against the current Library,
completed this explanation and submitted the pair. It retains every
field, valuation, topology, nonarchimedean local field and
connected-reductive quantifier of the target statement.
The underlying group scheme, rational-character lattice and actual
valuation image are the shared constructions. No additional finite-rank,
splitting or characteristic-zero premise is introduced.

Write `Lambda = Additive (rationalDiscreteValuationImage G)`,
`V = Hom_Z(Lambda,C)`, `L = log q`, and
`P = (2*pi*i/L) Hom_Z(Lambda,Z)`. The proof uses the actual period range
`rationalImagePeriodLattice G`. The imaginary subgroup `I` consists of
functionals with zero real part at every actual image element, and its
period subgroup `P_I` is the inverse image of `P` under `I -> V`.
The topology on `V` is the published pointwise topology; `I`, `P` and
`P_I` have inherited subgroup topologies. The quotient `I/P_I` has the
standard additive-group quotient topology. Both character spaces keep
their existing compact-open subgroup topologies. The canonical point
space has `rationalPointTopology F G.X`. The exponential is exactly
`E(lambda)(a) = exp(-lambda(a)*L)`.

The module imports the independently published
`Langlands.Representation.Plancherel.RationalComplexParameterQuotient`
by Lean name, obtaining its complex open quotient theorem and the
algebraic period-fiber and unitary-image theorems from
`Langlands.Representation.Plancherel.RationalComplexParameter`.
These proved results are dependencies, with no new hypothesis in the
final theorem.

The proof first places the actual periods in the finite
coordinates of the shared actual-image basis. The resulting map from
a finite product of integers is a closed embedding: integer inclusion
in the complex numbers is a closed embedding, multiplication by the
nonzero period is a homeomorphism, and finite coordinate evaluation is
the published parameter homeomorphism. Its range is exactly the actual
scaled integer-dual range, using extension from the same integer basis.
The embedding's range is closed and homeomorphic to the discrete finite
integer product, proving both assertions about the original periods.

The inclusion of the restricted periods into the original period
group is an embedding, since both composites into the complex
parameter space use their inherited subgroup topologies. Discreteness
therefore passes to the restricted periods. Their closedness is the
continuous preimage of the original closed period range.

The existing unitary-preimage theorem says that a complex parameter's
exponential is unitary exactly when its real part vanishes. This
identifies the imaginary subgroup with the preimage of the unitary
character subgroup. Mathlib's `IsOpenQuotientMap.restrictPreimage`
restricts the complex exponential's open quotient map to that preimage.
Composing with the equality-induced homeomorphism gives the actual
imaginary exponential's open quotient property.

Equality of two imaginary exponentials reduces to equality of their
underlying complex exponentials. The existing exact period-fiber
theorem then identifies their difference with an element of the
restricted original period subgroup. A quotient lift defines the map
from the actual additive quotient to unitary characters. The fiber
criterion proves injectivity, and the open quotient map's surjectivity
proves surjectivity of the lift. Quotient continuity and openness give
the homeomorphism; its value on each projected parameter is
definitionally the prescribed exponential.

The already constructed compact unitary character group transfers its
compactness across the inverse of this homeomorphism. Finally,
connected reductivity supplies affineness and smoothness, allowing the
canonical rational-point character topology. The existing unitary
image-to-unramified multiplicative homeomorphism transports the open
quotient map and composes with the quotient homeomorphism. The
prescribed value follows from the image-character value already
proved. The final theorem assembles precisely these nine conclusions.

The source is David Renard, *Représentations des groupes réductifs
p-adiques*, French version dated 9 July 2026, V.3.20, printed p.116/PDF
p.122, registered as `renard-2026-representations-groupes-reductifs-padiques`,
SHA256 `7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`.
The implemented proof gives an explicit topological formulation of the
source's lattice and compact imaginary-torus assertions, using finite
coordinates for the periods and restriction of the complex quotient
map. It proves no algebraic representability, smooth submanifold,
tensor-space or split-center comparison assertion, and it does not prove
the separate pure-tensor norm formula. The explicit closedness, open
quotient maps and commuting homeomorphisms are derived topological
conclusions of the cited passage, rather than separately numbered source
assertions. The normalization remains the published one: the normalized
real part of a lift is `-log norm/log q`, and raw logarithmic modulus is
`-log q` times that real part. In particular, their vanishing conditions
agree, which is the unitary criterion used here.
