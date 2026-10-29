# Actual matrix analytic assertions and transpose Fourier data

This module defines propositions for the matrix analytic assertions and their
normalized functional equation. It uses the actual integrals and bi-smooth
coefficient family from `GodementJacquet.Zeta`. Every actual rank is
`d = n+1`, including `n=0`. The field and complex representation carrier have
independent arbitrary universes. All definitions remain meaningful for reducible
representations; none asserts that the propositions hold for them.

## Original sources and convention adaptation

The principal source is Roger Godement and Hervé Jacquet, *Zeta Functions of
Simple Algebras*, Lecture Notes in Mathematics 260 (1972), registered as
`godement-jacquet-1972-zeta-simple-algebras`, SHA256
`86a8900900504adeb5757a04b5bb8a8754e6ef00b0fff49754096d371f59d568`.
The retained original is
`/home/taskhub/central-library/Godement-Jacquet--Zeta functions of simple algebras (book)--1972.pdf`.
Theorem 3.3 and its surrounding discussion are printed pages 30–36,
one-based PDF pages 40–46. Its four assertions supply the common convergence
bound, Laurent-polynomial normalized values, generation, and normalized
functional equation with an epsilon monomial. Printed page 31 defines an Euler
factor as `P(q^(-s))⁻¹` with `P(0)=1`; printed pages 31–33 discuss the
generated Laurent module and uniqueness. Printed pages 33–34 explain that the
assertions can be formulated for admissible representations with scalar central
quasicharacter, and need not hold if irreducibility is dropped.

The Fourier and coefficient conventions here follow H. Jacquet,
I. I. Piatetski-Shapiro and J. Shalika, *Automorphic Forms on GL(3) I* (1979),
printed page 177, one-based PDF page 10, equations (1.1.1)–(1.1.2), registered
as `jps-1979-gl3-i`, SHA256
`6446822f267f9f95156ce7a193409209e56ce7858ed6d3d350480e73f35b1aa5`.
The retained original is
`/home/taskhub/central-library/Jacquet-Piatetski-Shapiro-Shalika--Automorphic Forms on GL(3) I--1979.pdf`.
That page explicitly changes the original Godement–Jacquet Fourier transform
by transposing its argument:

`ΦHat(x) = ∫ Φ(y) ψ(Tr(y * transpose x)) dy`.

It simultaneously uses `fIota(g) = f(transpose(g⁻¹))`. The source invokes an
equivalence with the contragredient in its admissible irreducible setting.
Here `coefficientIota` is only this explicit transformation of functions.
Defining it proves no equivalence of representations or coefficient spaces,
particularly for a reducible carrier. The matrix equation uses central scalar
`1` and sign exponent `0` in the existing Rankin–Selberg equation, as in
the displayed 1979 formula. This convention adaptation is not a proved
analytic or representation-theoretic bridge.

The unshifted matrix integral and the Laurent variable also agree with
H. Jacquet, I. I. Piatetski-Shapiro and J. A. Shalika,
*Rankin–Selberg Convolutions* (1983), Section 5.2, printed pages 420–421,
one-based PDF pages 55–56, registered as `jpss-1983-rankin-selberg`, SHA256
`d9feed6388ca5acf02ecc6a8cce984871a7c28f062ff441e45a71fa2d8962245`.
Its retained original is
`/home/taskhub/central-library/Jacquet-Piatetski-Shapiro-Shalika--Rankin-Selberg Convolutions--1983.pdf`.
Sections 5.3–5.4, printed pages 422–423 / PDF pages 57–58, pass to actual
coefficient-model quotients and a generic constituent before the induction
and functional-equation comparison. They do not give an unconditional matrix
functional equation for an arbitrary reducible carrier.

Godement–Jacquet printed pages 30–45 were read in extracted text, with the
formulas on pages 30, 31 and 36 checked visually. The cited 1979 page and
1983 pages 420–423 were read visually. No source-specific registered errata
note was found in the project, Library or literature errata-note locations
or the literature pointers consulted.

## Exact definition correspondence

`coefficientIota f` is `g ↦ f(GeneralLinear.inverseTranspose (n+1) F g)`.
The set `iotaMatrixRationalValues q abv μ σ` ranges over all
`Φ : MatrixTestFunction n F` and actual `f : biSmoothMatrixCoefficients σ`,
requiring `HasShiftedRationalValue q abv μ Φ (coefficientIota f.val) R`.
Thus its functions come from the original coefficient family. It is not a
set of values of unrestricted functions or a redefined contragredient.

`MatrixConvergesOnRight abv μ σ` has quantifier order
`∃ a : ℝ, ∀ Φ, ∀ f : biSmoothMatrixCoefficients σ, ∀ s`,
followed by `a < s.re → MatrixConverges abv μ Φ (s+jpssShift n) f.val`.
The bound is common to all tests and coefficients. The analogous
`IotaMatrixConvergesOnRight` uses `coefficientIota f.val` with the same
quantifier order. Each side can have its own common bound; together the
two bounds can be replaced by their maximum.

`IsMatrixNormalizedGenerator q abv μ σ P` applies the published
`RankinSelberg.IsNormalizedGenerator` to exactly
`matrixRationalValues q abv μ σ`. The transformed version
`IsIotaMatrixNormalizedGenerator` applies it to exactly
`iotaMatrixRationalValues q abv μ σ`. In either case the meaning is
`P.coeff 0 = 1` and equality of the Laurent span with the module generated
by `(algebraMap (Polynomial ℂ) RationalFunctions P)⁻¹`.
This is a property of the proposed polynomial; no polynomial or continuation
is selected by default.

`MatrixAnalyticAssertions q abv μ σ P` combines the common convergence
predicate, existence of a `HasShiftedRationalValue` for every test/coefficient
pair, and `IsMatrixNormalizedGenerator` for the proposed `P`.
`IotaMatrixAnalyticAssertions` combines the corresponding three transformed
conditions. The rational-value relation reuses
`RankinSelberg.HasRationalContinuation`, including actual agreement with the
shifted integral and denominator nonvanishing on a right half-plane.
These conjunctions and value-set packages are internal formulations of the
source's assertions, not claims that the assertions are true.

`MatrixFourierPair ψ ν Φ ΦHat` requires, for every full matrix `x`, both
integrability of
`y ↦ Φ(y) * ψ.complex (rectangularPairing y x)` and equality
`ΦHat x = rectangularFourierIntegral ψ ν Φ x`.
Here `rectangularPairing y x = ∑ i, ∑ j, y i j * x i j`, which is
`Tr(y * transpose x)` by expanding the diagonal of the product.
The measure is exactly `RankinSelberg.rectangularMeasure ν (n+1) (n+1)`.
The raw rectangular integral is reused, including its plus sign, with no
new transform or measure. Actual integrability prevents a totalized integral
at a nonintegrable function from certifying a Fourier pair. The relation
alone asserts neither a Schwartz Fourier witness nor a Fourier equivalence.

`NormalizedMatrixFunctionalEquationData q ψ ν abv μ σ P PDual c m`
first includes both analytic assertions, for `P` and `PDual` respectively.
It then requires `∀ Φ, ∃ ΦHat`, with `MatrixFourierPair ψ ν Φ ΦHat`,
and for every original actual coefficient and every pair of continuations
`R,RDual` of the corresponding shifted integrals it requires
`RankinSelberg.NormalizedFunctionalEquation q P PDual 1 c 0 m R RDual`.
In particular, for every `s` where the two respective denominator evaluations
are nonzero, the equation is

`PDual(q^(-(1-s))) * RDual(q^(-(1-s)))`
`= c * (q^(-s))^m * P(q^(-s)) * R(q^(-s))`.

The fixed parameters are `c : ℂˣ` and `m : ℤ`. They and the two polynomials
are independent of the test and coefficient. The Fourier witness may depend
on `Φ` and is chosen before quantifying over coefficients. Both analytic
assertions guarantee actual continuations for every pair, including for
that Fourier witness, so a universal implication over nonexistent Fourier
pairs or nonexistent continuations cannot certify this package.

## Spectral and measure conventions

The three parameter conventions are distinct and fixed:

- `matrixIntegral abv μ Φ s f` has determinant exponent `s`.
- A continuation `HasShiftedRationalValue ... R` has integral exponent
  `s+(d-1)/2 = s+n/2`, with `jpssShift n = (n : ℂ)/2`, and rational
  argument `spectralPoint q s = q^(-s)`.
- The transformed side of the functional equation evaluates its continuation
  at `1-s`, hence its matrix integral has exponent `1-s+n/2` and rational
  argument `q^(-(1-s))`.

The generic definitions expose the supplied group measure `μ`, absolute value
`abv`, spectral base `q`, character `ψ`, and scalar additive Haar measure `ν`
where relevant. They require no irreducibility, admissibility, scalar central
character, self-duality, or extra relation between these inputs merely to
form the propositions. Such hypotheses belong to later theorem statements.

The `Padic` namespace supplies wrappers for `iotaMatrixRationalValues`,
both common convergence predicates, both normalized-generator predicates,
both analytic-assertion predicates, `MatrixFourierPair` and
`NormalizedMatrixFunctionalEquationData`. They use
`F.canonicalTopologicalData` for topology and local-field structures, canonical
Borel structures on the field and general linear group,
`normalizedAbsoluteValue F.canonicalTopologicalData`, the canonical residue
cardinality, and `generalLinearHaar F.Carrier n`, consistently with `Zeta`.
The Fourier wrappers still take `ψ` and `ν` as inputs and preserve `ν`
exactly. They neither choose a self-dual scalar measure nor rescale it.
Later existence and induction statements must retain actual self-duality
as a premise.

## Scope of the internal packages

Theorem 3.4, printed pages 36–45 / PDF pages 46–55, is a later conditional
induction theorem. Its hypotheses include admissibility and scalar central
quasicharacters for the blocks and the analytic assertions for both blocks and
their contragredients. Printed page 38 factors the full self-dual measure;
pages 40–42 use a finite expansion and functional equations; pages 43–45
establish the reverse generation inclusion. None is a conclusion of this
module. The transpose convention still requires separate analytic and
representation-theoretic comparison when used to formulate that theorem.

This module contains definitions only. It proves no analytic-data existence,
matrix Fourier closure or inversion, rationality, common denominator,
coefficient equivalence, product-ideal identity, functional equation, or
multiplicativity theorem. It also selects no local factor.
