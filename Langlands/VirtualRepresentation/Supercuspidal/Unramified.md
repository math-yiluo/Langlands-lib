# Full unramified twists and supercuspidal orbit classes

The namespace `Langlands.VirtualRepresentation.PadicSupercuspidal` constructs
unramified twisting on the actual positive-rank supercuspidal basis over a
`PadicField F`, using its canonical topology. Field universe `uF` and
representation-carrier universe `uV` are independent. Representation carriers
can be infinite-dimensional. Degree means the size of the general linear group,
extended with integer coefficients.

## Sources and derivation

Henniart, *Une preuve simple des conjectures de Langlands pour GL(n) sur un
corps p-adique* (2000), section 1.1 and footnote 1, printed p.439, specifies the
actual supercuspidal isomorphism classes and distinguishes continuous complex
quasicharacters from unitary characters. Section 1.2(2), p.440, uses twisting by a
field quasicharacter composed with determinant; section 1.3 ranges over all
unramified quasicharacters. Sections 2.5–2.6, p.446, define the free integral
supercuspidal lattice, its degree and coefficient pairing, and extend twisting
to virtual elements. The registered source is `henniart-2000-simple-proof`,
SHA-256 `be283c3e8187f1eed365537c72379c3e06e7791756954c2ac783c6beea2979de`.

This module is derived infrastructure. It specializes the published actual
class and lattice twists to `canonicalTopologicalData.determinantUnramifiedCharacter`.
That character is `g ↦ z ^ ord(det g)` for every `z : ℂˣ`, with the chosen
uniformizer of order +1. The imported `unramifiedCharacterEquiv` proves that
these parameters exhaust the field characters trivial on valuation units;
continuity and open kernels are already proved there. Thus the orbit action
includes the entire complex unramified family, with both magnitude and phase.
The explicit quotient, integral pushforward and rank descent are internal
constructions using Mathlib's group-action quotient and finite-support maps.
No correspondence or local-factor identity is used to construct them.

## Basis and lattice twists

`unramifiedTwistBasisEquiv F z` applies the genuine determinant-character twist
in each positive rank, with its inverse-character inverse. The required open
kernel and triviality on the determinant kernel are provided by the canonical
field construction; they are not extra assumptions on the caller. The rank is
unchanged. The identity, multiplication and inverse formulas follow from the
published class-twist laws and the corresponding character identities.
Composition applies the `w` twist first, then the `z` twist, and equals the
`z * w` twist.

`unramifiedTwistLatticeEquiv` is `Finsupp.domLCongr` on that equivalence, over
`ℤ`. Singles and generators move to the twisted basis index. Evaluation at
matched indices retains exactly the original coefficient. The identity,
composition and inverse laws are proved. Degree, the integral coefficient
pairing, and nonnegative coefficients are preserved, using the ambient
supercuspidal lattice laws. The pairing here is defined on a specified basis;
this is not an identification with a representation-theoretic Hom dimension.

`realPowerTwistBasisEquiv_eq_unramified` embeds the existing normalized
real-power twists into this full family. Its parameter is the real-power field
character evaluated at the existing uniformizer unit. The proof rewrites the
actual determinant characters, without choosing a complex logarithm.

## Actual orbit data

`unramifiedTwistAction` packages the established identity and multiplication
laws as a `MulAction ℂˣ` on the actual supercuspidal basis. It is an explicitly
selected action, not a global typeclass instance. `UnramifiedOrbitClasses` is
its genuine Mathlib orbit quotient, and `unramifiedOrbitClass` is the quotient
map. `unramifiedOrbitClass_eq_iff` says that two images coincide exactly when
some `z : ℂˣ` twists the second basis class into the first. Twisting therefore
does not change the orbit image.

`unramifiedOrbitMap` adds the integer coefficients within each orbit. Its
single-value formula and its invariance under twisting are proved by linear
finite-support induction. It is a map of lattices and is not asserted to be
injective or to preserve the coefficient pairing.

`unramifiedOrbitRank` descends the positive group rank through the quotient:
an orbit relation supplies a twist witnessing equality of the two basis
classes, and applying `Sigma.fst` proves equality of their ranks.
`unramifiedOrbitRankStratum` is the set of orbit classes of a specified positive
rank. `unramifiedOrbitDegree` extends orbit rank to an integer-linear degree,
and `unramifiedOrbitDegree_map` proves that collecting coefficients by orbits
preserves the original degree. There is no finiteness assertion or `Fintype`
instance on these strata.

## Genuine unitary restriction

For a parameter with `‖(z : ℂ)‖ = 1`,
`unitaryUnramifiedTwistBasisEquiv` uses the published preservation and reflection
of existence of an invariant positive definite Hermitian form. Its underlying
basis map is the same actual unramified twist. The identity, product and inverse
laws follow by subtype equality from the ambient laws; norm one for the product
and inverse follows from complex norm arithmetic.

`unitaryUnramifiedTwistLatticeEquiv` reindexes the integral lattice on exactly
this unitary subset. Singles, coefficients, identity, composition and inverse
laws are proved. Inclusion into the full lattice commutes with twisting; the
unitary degree, coefficient pairing and nonnegative coefficient condition are
preserved. No topology, norm or completeness structure is imposed on the
representation carrier to define its positive invariant form.

These constructions do not establish finiteness or transitivity of orbit
strata, supercuspidal contragredient closure, local-factor compatibility,
correspondence existence, or spanning by weakly associated global objects.
Those remain separate obligations.
