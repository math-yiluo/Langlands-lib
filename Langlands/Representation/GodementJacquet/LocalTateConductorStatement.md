# Scalar Tate theory with its principal-unit conductor

`Langlands.GodementJacquet.LocalTateConductorStatement` is an unproved proposition
over an arbitrary nonarchimedean local field `F`, in one unrestricted field
universe. It includes fields of positive characteristic. The character is an
actual continuous homomorphism `χ : Fˣ →* ℂˣ`.

The normalization data are the residue cardinality `q`, a uniformizer `ϖ`, and an
absolute value `abv` satisfying `abv ϖ = q⁻¹` and `abv x = 1` on valuation units.
The additive character `ψ` has conductor `O` in the existing
`Conductor.HasIntegerConductor` sense, and `ν` is the supplied additive Haar
measure self-dual for the actual plus-sign Fourier transform. Both the field
and its unit group carry their Borel measurable structures. The multiplicative
measure throughout is the existing `localMultiplicativeHaar F`, which gives
`Oˣ` mass one.

The conclusion derives a natural number `a` characterized by triviality of
`χ ∘ determinant` on `Conductor.levelSubgroup F 0 a` and by a nontrivial value on
every smaller level. In rank one these concrete subgroups are `Oˣ` at level zero
and `1 + m^a` at positive levels: this follows from the existing entrywise
congruence definition, with the determinant equal to the unique matrix entry.
Thus `a` is the usual principal-unit conductor exponent, with `a = 0` precisely
in the unramified case. Its existence and this characterization are conclusions,
not analytic or epsilon-factor hypotheses.

For each of `χ` and `χ⁻¹`, the statement asserts `ScalarMellinAnalyticData` for
weight one. This means a common right half-plane of absolute convergence for
all Schwartz--Bruhat tests, rational continuation of each actual integral, and
a common Laurent denominator. The two explicit polynomials are

`P(X) = 1 - χ(ϖ) X`, `PDual(X) = 1 - χ(ϖ)⁻¹ X` if `a = 0`,

and `P = PDual = 1` otherwise. Each is an `IsNormalizedGenerator` of its actual
`scalarMellinRationalValues` family. This identifies the Laurent span with the
span of its reciprocal and normalizes its constant coefficient to one; it does
not introduce an independent factor function.

There is one nonzero complex constant `c`, chosen before every test `Φ`. Each
test has a Schwartz--Bruhat transform `Φhat` satisfying integrability and

`Φhat(y) = ∫ ψ(x y) Φ(x) dν(x)`.

For every pair of actual rational continuations `R` and `RDual`, the conclusion
is the existing `NormalizedFunctionalEquation q P PDual 1 c 0 a R RDual`.
Equivalently, away from their poles,

`PDual(q^{-(1-s)}) RDual(q^{-(1-s)}) =
 c q^{-a s} P(q^{-s}) R(q^{-s})`.

There is no sign scalar since the sign exponent is zero. Continuations exist
by the analytic conclusions, so the universal functional equation is not being
asserted only for an empty family. No continuation, normalized generator,
functional equation, conductor exponent, or representation-theoretic
newvector conclusion is assumed.

## Sources and translation

John Tate, *Number theoretic background*, in *Automorphic Forms,
Representations and L-Functions*, Proc. Sympos. Pure Math. 33, Part II (1979),
pp. 3--26, source `tate-1979-number-theoretic-background`, SHA-256
`c890894fe19783890cc4def2c5bf92a18d71619acf8ba7005aefce4984fe70d6`:
printed p. 13, equation (3.1.3), gives the nonarchimedean Euler factor;
p. 13, the Fourier display and (3.2.1), give the plus-sign normalized local
functional equation; pp. 13--14, (3.2.6)--(3.2.6.3), define the principal-unit
conductor and give the exact unramified-twist exponent. These passages explicitly
allow nonarchimedean `F`, without restricting its characteristic.

Substitute `χ |·|^s` in Tate's formulas. Its dual character is
`χ⁻¹ |·|^{1-s}` and its Euler polynomial is the displayed `P` evaluated at
`X = q⁻ˢ`. Tate's twist law (3.2.6.3) gives the epsilon multiplier
`ε(χ, ψ, ν) q^{-(a(χ)+n(ψ))s}`. Here `HasIntegerConductor ψ` means `n(ψ) = 0`,
so `c = ε(χ, ψ, ν)` and the exponent is exactly the derived `a`.

The explicit Laurent-span and common-half-plane packaging records the usual
scalar local-zeta interpretation in the Library's concrete predicates. Tate's
*Fourier analysis in number fields and Hecke's zeta-functions*, in Cassels and
Fröhlich, *Algebraic Number Theory* (1967), Chapter XV, source
`tate-1967-thesis`, SHA-256
`01259375a6275b726e836ce209cee40ed6f98a5cefe1aa5ad40f2ad07a63169e`,
§2.4, Theorem 2.4.1, printed pp. 314--315, and §2.5, printed pp. 319--322,
provides the local functional equation and scalar local computations. Its
number-field presentation alone is not a justification of the
positive-characteristic scope; the unrestricted Corvallis formulas above fix
that scope and the elementary local-integral interpretation supplies the same
analytic and Laurent-span conclusions.

## Consumer boundary

This is a scalar prerequisite for the rank-one clause of
`Conductor.EssentialConductorStatement`. It does not identify the scalar
integrals with the JPSS coefficient-model integrals or transport their Haar
measures. Those comparisons and the rank-one representation adapter remain
separate proof obligations. The higher-rank essential-vector existence,
analytic comparisons, invariance and fixed-space conclusions are also outside
this proposition. The existing p-adic `tateScalarFunctionalEquation` proves an
unspecified integer exponent from normalized-generator premises and therefore
does not prove this proposition.
