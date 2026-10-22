# Exhaustion of absolute H² by finite unramified extensions

Author: Worker 80.

`UnramifiedH2Exhaustion.{u}` states that every element of the actual continuous
absolute cohomology group `absoluteCohomology F.Carrier 2` belongs to the
range of `closureInflation F.Carrier E.field 2` for some finite unramified
Galois intermediate field `E` of `AlgebraicClosure F.Carrier`.
It applies to every prime and every finite extension `F` of the p-adic
numbers, in an arbitrary universe.

The existing `FiniteIntermediateExtension` packages the intermediate field
and its finite-dimensionality certificate. The existential Galois
certificate applies to that same field. Its `asPadicField` wrapper keeps
the field operations and uses the composite p-adic algebra map through
`F.Carrier`; it supplies no additional arithmetic hypothesis.

Unramifiedness is expressed by equality of the absolute ramification
indices of `F.canonicalTopologicalData` and
`E.asPadicField.canonicalTopologicalData`. Each index is the normalized
integer order of the common rational prime. For a compatible finite
extension of p-adic fields, equality of these absolute indices says the
relative ramification index is one. Their residue fields are finite and
therefore perfect. This uses the same arithmetic convention as the
published `UnramifiedUnitNorms` and `UnramifiedNormMembership` statements.
The statement uses constructed canonical local-field realizations, rather
than requiring realizations as inputs.

The map in the conclusion is exactly the published `closureInflation`.
Its source is ordinary cohomology of `Gal(E.field/F.Carrier)` with
coefficients in the actual units of `E.field`. It first inverts the proved
finite continuous-to-ordinary comparison and then applies the actual
continuous group-and-coefficient inflation to algebraic-closure units.
Membership in its additive range means that an actual relative
degree-two class maps to `x`; no cohomology carrier or comparison map is
replaced.

The chosen intermediate field and the closure have the base universe
`u`. This prerequisite does not assert the host theorem's
independent-universe finite-extension case. It also does not assert
injectivity of inflation, select a degree or Frobenius generator for `E`,
construct a local invariant, or give its compatibility with restriction.
Those are separate results. This file defines a proposition, with no proof.

## Source correspondence

Jean-Pierre Serre, *Local Fields*, Greenberg English translation, Springer
GTM 67 (1979), Chapter XII, section 3, Proposition 3, printed page 184 /
PDF page 189. Registered source: `serre-1979-local-fields`, SHA256
`109b461d42915da70771c70c4b551a363fc1f33412331ae2671c5c85be433112`,
retained at `/home/taskhub/central-library/Serre--Local Fields--1979.pdf`.
Worker 80 read this original page, the supporting unramified-splitting
Theorem 1 in XII.1 (printed page 181 / PDF page 186), and X.3–4
(printed pages 154–156 / PDF pages 160–162). No project errata entry for
this source was present when checked.

Serre's base field `K` is `F.Carrier`; his finite unramified Galois field
`L` is `E.field`. Proposition 3 states that the Brauer group is the union
of the relative groups `H²(L/K)` over those fields. Here that union is
written elementwise as membership in the image of the existing inflation.
Theorem 1 explains the arithmetic content: every class splits over a
finite unramified extension. The p-adic case satisfies the source's
completeness, discrete valuation and perfect residue-field hypotheses.

The source's Brauer group is the degree-two absolute Galois cohomology
defined in X.4, and X.3 relates its finite-stage description to continuous
cochains. The corollary to X.4 Proposition 6 supplies the finite-to-absolute
injection identifying the relative group with its image. The Lean target
uses only the range, so it leaves that injectivity to the separate
`AbsoluteH2InflationExactness` target.

A proof must establish the arithmetic splitting and all finite-stage and
continuous comparison arguments for these actual maps. Neither the
source citation nor the imported residue construction supplies an
unproved Lean identification with a central-simple-algebra Brauer group.
