# Spectral values of a supplied common-closure system

This module constructs spectral twists on the actual continuous exact virtual
groups and evaluates an explicitly supplied system satisfying
`NonabelianSystem.IsSystem`. It keeps Deligne's measure-dependent constant and
Langlands' half-shifted self-dual-measure convention distinct. No local-constant
system or self-dual measure is chosen.

`baseDegree F E` restricts the actual geometric integer degree of the base Weil
group to the subgroup fixing `E`. `baseCardinality F` is the cardinality of the
actual residue field of `F`, cast to the real numbers. Its positivity follows
from the nonempty finite residue field. The degree and cardinality are both those
of the base field: the degree has not been renormalized over `E`.

`character F E s` is the existing continuous unramified character with value
`exp(-s log q_F)` at base degree one; `character_apply` exposes its value at each
actual subgroup element. `virtualTwist` is the published continuous exact-twist
automorphism for this character. The zero, composition and dimension identities
are direct specializations of the published spectral-twist identities. In
particular, it is an operation on the actual short-exact quotient, with no
semisimplicity or selected irreducible decomposition.

`conditionalDeligneValue F e ε hε E ψ μ x s` is the actual supplied assignment
`ε` evaluated on `virtualTwist F E s x`. Its arguments retain the specific
reciprocity family, assignment, and proof of the full common-closure system
property. Its value at spectral parameter zero is the original constant.
This is a conditional construction; it does not construct an unconditional
epsilon function or prove the system-existence proposition.

`IsSelfDual` specializes the existing intrinsic Fourier condition to the
canonical intermediate-field topology and Borel space. Hausdorffness uses
`TopologicalData.fieldT2`; total disconnectedness follows from Mathlib's
nonarchimedean additive-group theorem after transporting the valuation topology
along `Valuation.toTopologicalSpace_eq`. These are proved certificates, with no
new topological hypothesis. The self-duality condition uses the
plus-sign transform, requires convergence of the second transform, and requires
Fourier squared to be reflection. `SelfDualMeasure` is the subtype of actual
regular Haar measures satisfying it. No element of this subtype is chosen.

`conditionalLanglandsConstant` evaluates the Deligne spectral value at `1/2`
using a supplied self-dual measure. `conditionalLanglandsValue` applies that
constant to the twist by `s - 1/2`. The theorem `conditionalLanglandsValue_eq`
uses the constructed exact-twist composition law and the identity
`1/2 + (s - 1/2) = s`, so the result is Deligne's spectral value at `s` with
that same self-dual measure. It proves no measure comparison or functional
equation, and it does not use the disputed printed measure-ratio formula.

The normalization source is John Tate, *Number theoretic background* (1979),
section 3.6, equations (3.6.1) and (3.6.4), printed page 17, retained Part II PDF
page 26. Literature ID `tate-1979-number-theoretic-background`, SHA256
`c890894fe19783890cc4def2c5bf92a18d71619acf8ba7005aefce4984fe70d6`.
The retained original was read, and the two distinct shifts are preserved.
The actual degree character and exact quotient twist are derived specializations
of `Weil.Local.Assembly`, `LocalFactor.SpectralTwist`, and
`VirtualRepresentation.ExactTwist`. The self-dual measure predicate comes from
`HarmonicAnalysis.Basic`.

The scope remains finite p-adic fields, complex coefficients, actual fields in
one specified common closure, and a fixed carrier universe closed under
induction. The module makes no comparison with separately constructed Weil
groups and no cross-closure descent assertion. It does not yet multiply by the
Weil–Deligne invariant-quotient correction. In that later construction a geometric
Frobenius over `E` generally has base degree greater than one, and its spectral
correction uses the residue cardinality of `E`, not `baseCardinality F`.
