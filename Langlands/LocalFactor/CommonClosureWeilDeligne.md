# Conditional Weil–Deligne factors in an actual common closure

This module specializes the existing invariant-kernel Euler factor and
invariant-quotient determinant to the actual Weil subgroup fixing a finite
intermediate field. It combines the quotient correction with an explicitly
supplied local-constant system. The result is named `conditionalEpsilonValue`;
no unconditional nonabelian epsilon function is constructed.

## Arithmetic inputs and Frobenius

Fix a finite p-adic field `F` and `E : CommonClosure.Extension F`.
`normCharacter F E` is the continuous restriction of
`Weil.Local.localNormCharacter F` to `CommonClosure.weilSubgroup F E`.
Its value is the actual base residue cardinality raised to the negative
base geometric degree, as recorded by `normCharacter_apply`.
`inertia F E` is the kernel of that restricted degree homomorphism.
It is a normal subgroup by the general kernel instance.

`residueCardinality F E` is the actual residue cardinality of the canonical
topological field `CommonClosure.fieldData F E`, cast to the reals. Its
positivity follows from the published fact that the residue cardinality is
greater than one. The degree and cardinality in the restricted ordinary
spectral character remain those of `F`; the cardinality in the Euler and
quotient evaluations below is that of `E`.

`GeometricFrobenius F E` is the subtype of elements `Phi` of the actual
fixing subgroup satisfying
\[
  \nu_F(\Phi)=q_E^{-1}.
\]
This is the precise normalization required of the supplied element. The
module asserts no existence of such an element and makes no selection.
`degree_eq_of_normCharacter_eq` takes complex norms of the equality of norm
values and uses injectivity of integer powers of the positive real number
`q_F > 1`. It follows that two such elements have the same restricted base
degree. `frobenius_coset` then proves that their quotient belongs to the
actual inertia kernel.

`Pair F E` is the existing finite-dimensional complex
`WeilDeligneRepresentation` on this subgroup, with covariance character
exactly `normCharacter F E`. The group universe is `uF` and the carrier
universe is `max uF uV`, as required by the common-closure exact virtual
groups. Continuity of the underlying ordinary representation is an explicit
argument where its exact virtual class is used. `underlyingClass` constructs
that class using the actual continuous representation, and its invariance
under pair equivalence follows from the existing exact-quotient relation.

## Euler factor and quotient correction

For a supplied pair and geometric Frobenius, `rationalLFactor` is the
existing rational reciprocal
\[
  \det(1-Xr(\Phi)\mid(\ker N)^I)^{-1}.
\]
It retains the rational poles. `SpectralRegularPoint` requires the Euler
denominator at `exp(-s log q_E)` to be nonzero, and `spectralLValue` takes
only such a point and returns a nonzero complex unit. These definitions
reuse the generic construction rather than evaluate a rational reciprocal
as an everywhere finite complex function.

Write \(Q=V^I/(\ker N)^I\). `quotientValue` specializes the already
constructed `WeilDeligne.quotientCorrectionValue` at the nonzero unit
\(q_E^{-s}=\exp(-s\log q_E)\). The theorem `quotientValue_det` exposes
exactly
\[
  \det\bigl(-q_E^{-s}r(\Phi)\mid Q\bigr).
\]
The quotient, induced operator and nonvanishing determinant are all the
actual constructions from `LocalFactor.WeilDeligne`. No scalar correction
is supplied as an independent input.

`conditionalEpsilonValue F e epsilon h E psi mu A hA Phi s`
is the product of
`CommonClosureSpectral.conditionalDeligneValue` on `underlyingClass A hA`
and this quotient value. Here `e` is the supplied reciprocity family,
`epsilon` is the supplied assignment, and `h` proves the full
`NonabelianSystem.IsSystem` property. The additive character and Haar
measure are the actual common-closure harmonic inputs. The ordinary
spectral value uses the actual restricted base norm twist; the correction
uses the intermediate-field cardinality and the supplied geometric
Frobenius over that field.

## Intrinsic identities and scope

`quotientValue_eq_of_equiv` uses invariance of the quotient polynomial
under the actual pair equivalence. `quotientValue_eq_of_frobenius` uses
the proved inertia-coset relation and the generic determinant invariance
under that relation. If monodromy is zero, the generic quotient has
dimension zero and determinant one; substituting these identities in the
correction monomial proves `quotientValue_eq_one_of_monodromy_zero`.

The three corresponding `conditionalEpsilonValue` theorems combine
these identities with invariance of the underlying exact class or with
unchanged ordinary input. They respectively prove invariance under pair
equivalence, independence of the supplied geometric lift, and reduction
to the ordinary supplied-system spectral value when `N = 0`.

The scope is finite p-adic fields, complex coefficients, the specified
common closure and the stated carrier universe. This module proves no
epsilon-system existence, reciprocity existence, self-dual-measure
existence, Frobenius existence, comparison with separately constructed
Weil groups, or cross-closure descent. It adds no functional equation,
tensor-pair factor or exact virtual dual. These limitations do not alter
the explicit mathematical inputs to the construction.

## Source and derived content

The source is John Tate, *Number theoretic background* (1979), section
4.1.6, printed page 21, retained Part II PDF page 30. Literature ID:
`tate-1979-number-theoretic-background`; SHA256:
`c890894fe19783890cc4def2c5bf92a18d71619acf8ba7005aefce4984fe70d6`.
The retained formula page was read directly. Its Euler reciprocal and
determinant on \(V^I/V_N^I\) are implemented in the imported generic
module and specialized here to the actual arithmetic objects.

The spectral determinant is the derived substitution `X = q_E^(-s)`
in the generic correction polynomial. The ordinary factor is the
separately specified fixed-character spectral twist. Tate's auxiliary
expression `epsilon(V) t^(a(V))` is not identified with that full
fixed-character value, which also depends on the additive character.
The norm restriction, Frobenius subtype, exact-class construction and
the elementary invariance proofs above are derived implementation
constructions using the named Library definitions and identities.
