# Unramified twist transport of certified pair L-polynomials

Worker 85, with Worker 352 contributing the spectral-rescaling instantiation.
The theorem `Langlands.RankinSelberg.unramifiedTwistLFactor` proves exactly
`UnramifiedTwistLFactorStatement.{uF, uV, uW}` from
`UnramifiedTwistStatement`. For every supplied complex exponent `u` and
character `χ(x) = |x|^u`, a certified polynomial `P` for a pair transports,
after twisting either representation, to
`P.comp (C ((q : ℂ)^(-u)) * X)`.

The field universe and the two representation-space universes remain
independent. The proof retains every canonical p-adic field, the supplied
unitary additive character and self-dual Haar measure, all positive ranks,
and both rank orders. It uses the actual supplied L-polynomial certificate;
it introduces no Whittaker-type or analytic-existence hypothesis. The
epsilon statement is a separate proposition and is not proved here.

## Provenance and imported results

This is a derived transport argument in the conventions of Jacquet,
Piatetski-Shapiro and Shalika, *Rankin–Selberg Convolutions* (1983),
registered as `jpss-1983-rankin-selberg`, SHA256
`d9feed6388ca5acf02ecc6a8cce984871a7c28f062ff441e45a71fa2d8962245`.
Section (2.4), printed page 387, gives the determinant-weighted integrals;
Theorem (2.7)(ii), printed pages 390–391, gives the normalized reciprocal
polynomial convention. The target's symmetric relation follows the
larger-rank-first convention of (2.12), printed page 403.
The transport theorem is derived from these definitions, rather than
quoted as a separate numbered theorem.

The implementation imports `UnramifiedTwistIntegrals`, which proves that
twisting either member multiplies the corresponding Whittaker functions by
`χ(det g)` and shifts the integral parameter from `s` to `s + u`.
Its equal- and unequal-rank zeta-set image identities transport the actual
convergence and continuation certificates. It also imports
`SpectralRescaling`, which constructs substitution `R(X) ↦ R(q^(-u) X)`
on rational functions, proves the continuation equivalence including
reduced-denominator nonvanishing on a right half-plane, and transports
normalized generators of the actual Laurent span.

## Implemented proof

`isPairLPolynomial_unramified_of_transport` first treats arbitrary
continuation and generator transport laws. For unequal ranks it unfolds the
pair certificate and applies the published zeta-set image identity to every
block indexed by `j` and `k`, in each twist position. For equal ranks it
uses the equal-rank image identities. The remaining rank order contradicts
the ordered-pair certificate. In every case the assumed generator law
transports the normalized polynomial along the same image equivalence.

`isPadicPairLPolynomial_unramified_of_transport` installs the canonical
topological and measurable structures. It preserves the certificate's
existence of a compatible quotient measure and applies the ordered-pair
argument for every compatible measure. Thus no choice of measure is
silently substituted for the universal measure condition.

`isPadicSymmetricLPolynomial_unramified_of_transport` unfolds the rank-order
selection. When the pair is reversed, the ordered argument is applied to
the reversed representations and its two conclusions are exchanged.
This preserves the two separate representation universes.

`unramifiedTwistLFactor_of_transport` specializes these constructions to
the actual residue cardinality, using its published strict lower bound
`1 < q`, and to the self-dual measure's underlying Haar measure.

Finally, `unramifiedTwistLFactor` supplies the algebraic laws intrinsically.
It chooses the underlying equivalence of
`rationalRescale (spectralShiftUnit q hq u)`.
`hasRationalContinuation_shift_iff` gives the exact continuation law.
`IsNormalizedGenerator.rescale`, followed by unfolding the value of
`spectralShiftUnit` and `spectralPoint`, gives precisely
`P.comp (C ((q : ℂ)^(-u)) * X)`. All transport hypotheses of the
intermediate assembly are therefore discharged in the final theorem.
