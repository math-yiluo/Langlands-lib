# Conditional pole comparison for actual witnessed relative pairs

This is a derived **statement target**, with no proof of
`RelativePolePairingStatement` in this file. It is the concrete pairing adapter
for H1, task `205503d3-82c7-4b1a-a4f0-90d02bbe9a2e`. Its conclusion concerns
generated integral spans at a finite place.

The index is the existing
`Langlands.VirtualRepresentation.RelativeGlobal.WitnessedGenerator F E c v`.
Each generator retains an actual relative Weil representation of `W_{E/F}`,
irreducibility and unitarity, a full cuspidal operator realization, a spectral
presentation, weak association, a place above `v`, a reciprocity candidate,
and a local Weil map satisfying `IsLocalRelativeWeilMap`. It also retains the
full effective unitary Weil expansion and the actual unitary supercuspidal
support of the full automorphic local component. The field universe, Weil
carrier universe and presentation-factor universe remain independent as in
the existing interface. The two number fields have the common universe
required by that interface; this adapter introduces no further identification.

`witnessedLocalClass` is the actual class obtained from the presentation and
its irreducibility and admissibility witnesses. The arithmetic distinguished
function is the actual `arithmeticPairLFactor` of the local pair class of the
first Weil representation and the local pair class of the **dual** of the
second. Each uses its own supplied characterized local map. The rational
function is evaluated by `RatFunc.eval` at the existing
`RankinSelberg.spectralPoint q s`, where `q` is the canonical residue
cardinality of `F_v`. This is the same `X = q^(-s)` convention as the factor
interfaces. Evaluation is totalized at poles; all subsequent order statements
refer to punctured germs, and distinguished-factor meromorphy is an explicit
hypothesis.

For every pair, `RelativePairFactorData` supplies an actual automorphic smooth
dual class for the second component and an
`IsAutomorphicPairLPolynomial` certificate for the first component paired with
that dual class. The certificate retains the actual representation and
Langlands-factor existence witnesses in that published relation. The
automorphic distinguished function evaluates the existing
`automorphicPairLFactor` constructor, namely the reciprocal of the certified
polynomial in `X`. Thus the distinguished functions cannot be arbitrary
functions merely labeled as local factors.

`RelativeCertifiedPoleComparisons` requires existence of a self-dual measure
for the supplied nontrivial additive character and, for **every** such
measure, existence of the full certified data. For those data the following
inputs are separate:

- meromorphy of both distinguished factors at zero;
- analyticity and nonzero value of every factor in each finite omitted-place
  set, with each auxiliary finite place quantified;
- analyticity and nonzero value of each separate boundary function;
- equality of the two completed punctured germs;
- identification of each distinguished order with minus the corresponding
  coefficient pairing, as an equality in `WithTop ℤ`.

The finite omitted-place sets and functions are supplied explicitly and may
differ on the two sides. Archimedean contributions and partial global factors,
when required for an application, must be included in the supplied boundary
functions and their unit proofs. No infinite product of local gamma factors
is formed. This target assumes the completed-germ identity: the finite
functional-equation comparison engine is responsible for deriving the
relevant local identities from actual global functional equations,
almost-everywhere matching and the prescribed auxiliary twist identities.
Those global functional equations, highly ramified stability and the
necessary existence inputs remain obligations of the parent program and
the factor owners. Boundary nonvanishing, including the global input used
by Henniart from Shahidi 1981, Theorem 5.2, remains an additional explicit
analytic input; omitted local regularity does not prove it.

The conclusion is equality of the actual local coefficient pairings for all
witnessed generators, equality of the integral relation kernels, and a unique
linear equivalence between the existing `weilImage` and `automorphicImage`.
The equivalence sends every witnessed Weil element to its automorphic
partner, preserves pairings and the existing degree maps, and sends each
positive-degree norm-one vector in its source span to a unique positive
target basis vector. The existing generator degree identities identify both
degrees with `rankIndex + 1`; they need not be assumed again. No ambient
spanning, numerical surjectivity, or local correspondence bijection follows
without further input. In particular, this is not a proof of
`AssociatedFactorStatement`.

The provenance is the pole-order argument and integral descent in
Henniart, *Une preuve simple des conjectures de Langlands pour GL(n) sur un
corps p-adique* (2000), sections 2.5–2.8, printed pages 445–448; the actual
factor comparisons motivating the hypotheses are in sections 2.3–2.4,
printed pages 443–445. The Lean formulation is an internal derived adapter
to the current Library, not a separately printed theorem. The intended proof
composes `PolePairingDescentStatement` with the published concrete
virtual-lattice algebra and the degree identities of `WitnessedGenerator`;
the actual analytic pole formulas are retained as inputs.
