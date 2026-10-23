# The lower-right Kirillov pairing quotient

This module defines the pairing equation of Shahidi, *Fourier transforms of
intertwining operators and Plancherel measures for GL(n)* (1984),
Proposition 1.2, printed page 74, using the lower-right upper-unipotent
quotient described below. It is a derived prerequisite for measure item 1
on pages 75–76. The source's literal primed-subgroup notation has a
compatibility problem; the chosen interpretation is explicit here.

## Source interpretation

Write `r = n + 1`, with `r` the rank of the representation. Page 71 embeds
`G_(r-1)` in the upper-left block and defines
`G'_(r-1) = w_r G_(r-1) w_r⁻¹`, where `w_r` is the antidiagonal permutation
matrix. As a subgroup, this is the lower-right block `diag(1, GL_n)`.
Page 74 literally displays `N'_(r-1) = w_r N_(r-1) w_r⁻¹`. With the
upper-unipotent convention of page 70, this is the **lower** unipotent
subgroup in that lower-right block.

Whittaker functions for the source's character satisfy `W(ug) = χ(u)W(g)`
for **upper** unipotent `u`. Consequently, the product
`W_v(g) conjugate(W_w(g))` is invariant under the upper unipotents, since
`χ` is unitary. This argument does not establish invariance under the literal
lower subgroup in the displayed definition of `N'_(r-1)`.

We therefore use the subgroup `N_r ∩ G'_(r-1)`, identified with `N_n` by
`a ↦ diag(1,a)`. This agrees with the equivariance of the Kirillov restriction
on page 71 when the smaller group is identified with the lower-right block
by this map. It also lies in the stabilizer of the first standard basis
vector used just before Proposition 1.2. Equivalently, this subgroup is
`w_r N^-_(r-1) w_r⁻¹`, where `N^-` denotes the lower unipotents in the
upper-left block. These matrix descriptions explain the interpretation;
this module proves the embedding and the necessary invariance directly,
without needing a formal equality with the subgroup intersection.

This choice is an inference from the source and its equivariance conventions,
not a claim of a published erratum. Worker 11 independently contributed the
source and matrix analysis supporting it. The module does not assert descent
for the literal lower-unipotent quotient. The transpose/inverse quotient
transport in measure item 1 on page 75 is a separate construction.

## Mathematical definitions

`kirillovInclusion n` is the group homomorphism `GL_n(F) → GL_(n+1)(F)`
given by the published insertion map `Bruhat.insert 0`, hence `a ↦ diag(1,a)`.
`kirillovInclusion_succ_succ` proves its lower-right entry formula, and
`kirillovInclusion_injective` proves that the embedding is faithful.
`kirillovUnipotent` sends an actual upper-unipotent matrix of the smaller
group to an actual upper-unipotent matrix of the larger group.

`KirillovQuotient n F` is the actual left quotient `N_n \ GL_n(F)`, using
`QuotientIntegration.LeftQuotient`. This type uses the equivalence relation
for left cosets, so descended functions must be invariant under left
multiplication by `N_n`.

For an algebraic complex representation `π` of `GL_(n+1)(F)`, a unitary
additive character `ψ`, and a Whittaker functional `ℓ` for its standard
character, `kirillovPairingFunction ψ n π ℓ v w a` is

`ℓ(π(diag(1,a))v) · conjugate(ℓ(π(diag(1,a))w))`.

`kirillovPairingIntegrand` is its actual quotient descent, rather than a
function on chosen representatives. Its evaluation lemma gives exactly
the displayed expression on the class of `a`.

Given a measurable structure and a measure `ν` on this quotient and an
invariant positive definite form `b` on `π`,
`IsKirillovPairingNormalized ψ n π ℓ b ν` requires, for every `v,w`,
scalar integrability of that descended function and the equation

`∫ q, kirillovPairingIntegrand ψ n π ℓ v w q ∂ν = b.inner w v`.

The Library form is conjugate-linear in its first slot, so reversing its
arguments matches the first-variable-linear pairing of Proposition 1.2.
The explicit integrability condition prevents use of the total Bochner
integral's default value for a nonintegrable function.

## Implemented proofs

The insertion entry formula is inherited from `Bruhat.insert`. Its upper
triangularity and diagonal-entry lemmas show that `kirillovUnipotent` lies
in the required subgroup. Extracting every lower-right entry from an
equality of inserted matrices proves injectivity.

For left multiplication by an upper-unipotent `u`, the representation law
and Whittaker equivariance multiply the two coefficients by the same
standard character value. Complex conjugation turns the combined factor
into `χ(u) conjugate(χ(u)) = 1`, using the norm-one character lemma.
This proves `kirillovPairingFunction_invariant` and supplies precisely the
hypothesis required by `QuotientIntegration.descend`.

The `integrable` and `integral_eq` lemmas project the defining conditions.
`measure_ne_zero` assumes a nonzero vector `v`. If `ν` were zero, the
diagonal integral would be zero; the pairing equation would give
`b.inner v v = 0`, contradicting positive definiteness. Thus the
nonzero-measure consequence has an explicit nonzero-vector hypothesis.

## Scope

The definitions permit arbitrary fields with a topology and arbitrary
algebraic complex representation spaces; no norm or topology on the carrier
is imposed. They make sense for `n = 0` as well. This algebraic generality
asserts no existence theorem outside the source's unitary supercuspidal
setting in Section 1, nor within it.

The supplied measure is not required here to be right-invariant, regular,
or compatible with Haar measures through a Weil formula. Its measurable
structure is supplied, and no measurability of the quotient action is
asserted. The definition includes neither existence of a normalized measure
nor the choice of the pairing from Lemma 1.1. Those conditions, the
`dn₁ dn₂` decomposition, and the remaining measure items belong to the
later full normalization relation. This module does not prove Proposition
1.2, analytic continuation, or the Theorem 5.1 comparison.
