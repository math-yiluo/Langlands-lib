# Scalar extraction and continuation for actual unramified families

This derived unit supplies an algebraic step toward Waldspurger IV.3, printed
p.285 / PDF p.51 of the registered original `waldspurger-2003-plancherel`
(SHA256 `4b6a6162cd0b3863703fb2f65d1698f926caf813114917f2084c16e38f2e30f7`).
There the opposite-intertwiner composite is scalar on a nonempty generic
irreducibility locus, and its scalar is continued rationally. The present
module proves the continuation step for a supplied rational endomorphism
family on actual unramified characters. It does not establish the required
generic irreducibility or construct the continued standard intertwiners.

## Extracting the scalar from the given operators

For a complex vector space `V`, a fixed vector `v` and an algebraic complex
linear functional `ell`, `UnramifiedOperatorFamily.endomorphismScalarCoefficient`
is the linear map

`T -> ell (T v)`.

No topology on `V` is used. If `ell v = 1`, its value on `c * id` is exactly
`c`. Consequently, a scalar endomorphism equals this extracted coefficient
times the identity. Every nonzero vector admits such a normalized functional,
by the algebraic dual separation result in Mathlib. A normalized pair thus
also excludes the zero vector space.

For an arbitrary norm-character family, `scalarCoefficient_numerator` takes
the existing `IsRationalOperatorOn` predicate for `A` and obtains two elements
`a,b` of the existing evaluation-generated regular scalar algebra, with
`b(chi)` nonzero at every parameter of the supplied region and

`b(chi) * ell (A(chi) v) = a(chi)`.

It uses the original whole-operator denominator. Applying the functional to
the fixed-vector numerator and the published `isPolynomialOn_scalar_iff`
gives the single regular numerator `a`. `IsRationalOperatorOn.scalar_part`
uses that same denominator to prove rationality of
`chi -> ell (A(chi) v) * id`.
The small polynomial subtraction law follows by applying the negative
identity linear map and the existing addition law.

## Uniqueness on actual character parameters

For the continuation results, `G` is a connected reductive group scheme over
an arbitrary-universe nonarchimedean local field of arbitrary characteristic.
A topology on its rational points and continuity of
`rationalValuationImageProjection G` are explicit. The norm family contains
all actual rational norm characters of `G`. These are precisely the inputs
of the published `rationalUnramifiedRegular_eq_zero_of_isOpen` theorem.
There is no splitness, quasisplitness or positive-rank restriction.

The parameter region `Omega` is any subset of the full unramified character
space. It contains an ambient open nonempty subset `D`. No openness of
`Omega` is needed. All families are defined on the corresponding subtypes.

`rationalUnramifiedPolynomial_eq_zero_of_isOpen` proves that a polynomial
vector family on `Omega` vanishing on `D` vanishes on all of `Omega`.
Apply any algebraic scalar functional to its finite vector expansion.
The resulting single regular scalar vanishes on `D`, so the published
actual scalar uniqueness theorem makes it zero globally. Algebraic dual
separation then gives zero for the original vector at every parameter.
There is no continuity assumption on the vector family or topology on its
carrier, and no hypersurface-divisibility premise is used.

`rationalUnramifiedOperator_eq_of_eqOn_isOpen` applies this result to each
fixed input vector after cross-multiplying the two rational families by
their original denominators. Both denominators are nonzero everywhere on
`Omega`, so the zero cross-multiplied difference gives equality there.
The source and target carriers have independent universes.

## Scalar continuation and choice independence

`rationalUnramifiedScalarContinuation` assumes a rational endomorphism
family `A` on `Omega`, a normalized pair `(v,ell)`, and scalarity of `A`
at each parameter of `D`. It compares `A` with its extracted scalar part.
Both are rational on `Omega` and agree on `D`, so operator uniqueness gives

`A(chi) = ell (A(chi) v) * id`

for every parameter of `Omega`. The numerator result above supplies a
regular numerator and a denominator nonvanishing on this whole region
for the extracted coefficient. The final theorem proves that two
normalized extraction pairs yield the same scalar throughout `Omega`.

## Provenance and remaining source obligations

The implemented route uses the existing finite-expansion rational-family
definitions, linear-map laws, the single-regular-scalar characterization,
the published actual Laurent uniqueness theorem, and Mathlib algebraic dual
separation. These are internal derivations motivated by IV.3; the module
does not identify its abstract family with Waldspurger's composite.

The generic scalarity hypothesis can later be supplied using Schur on an
appropriate generic irreducibility locus. It is an explicit mathematical
premise of this continuation lemma, not a permitted structural hypothesis
for the main Plancherel program. No irreducibility of general tempered
parabolic induction is imposed or proved. Construction and rational
continuation of the actual standard intertwiners, existence of the generic
locus, descent to the representation orbit, comparison of different
parabolics, nonvanishing and the IV.3 identities for `j`, and the V.2 density
`mu` remain separate obligations. This unit constructs no value at a pole
and makes no Plancherel completion claim.
