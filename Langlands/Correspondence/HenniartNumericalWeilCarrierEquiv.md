# Weil carrier universes in Henniart's numerical theorem

For a fixed p-adic field \(K\) and positive rank, `weilClassCarrierEquiv`
identifies the continuous irreducible classes of the actual local Weil group
at two independent complex representation carrier universes. The map uses
`FiniteRepresentation.continuousIrreducibleCarrierEquiv`.

To compare `HasArtinConductor` on the two classes, the proof chooses actual
representatives. The criterion for the class bijection gives a complex-linear
intertwining equivalence between them. The Artin conductor relation agrees
with the Artin exponent of any representative by
`hasArtinConductor_iff_artinExponent_eq`, and
`Weil.Local.artinExponent_eq_of_equiv` identifies the two exponents.
The character-twist comparison specializes the class bijection's twist
identity to `Weil.Local.unramifiedCharacter` with geometric Frobenius sent
to the same \(z \in \mathbb C^\times\) at both carrier levels.

`numericalInjectionWeilCarrierEquiv` transports the subtype of maps satisfying
`IsNumericalInjection` by precomposition with the Weil class bijection from
the new carrier level to the old one. The target supercuspidal class space
is fixed. Precomposition with a bijection preserves and reflects injectivity
and surjectivity. Conductor preservation follows from the Artin comparison,
and twist equivariance follows from the twist identity. Surjectivity of the
class bijection gives the reverse implications for the conductor and twist
conditions on all source classes.

`numericalSurjectivity_weilCarrierEquiv_iff` applies the transport uniformly
over all primes, p-adic fields and positive ranks. Combining it with
`numericalSurjectivity_carrierEquiv_iff` gives the equivalent numerical
surjectivity propositions for arbitrary pairs of representation carrier
universes at the same field universe. In particular,
`numericalSurjectivity_of_carrierUniversesZero` takes a proof with both
representation carriers in universe `0` and produces one at any two carrier
levels.

The numerical injection and surjectivity conditions are from Guy Henniart,
*La conjecture de Langlands locale numérique pour GL(n)*, Ann. Sci. Éc.
Norm. Sup. (4) 21 (1988), Théorème 1.2, p. 498, with the class domains in
§1.1 (`henniart-1988-numerical`,
SHA-256 `3de93884b6c4b26106d614e648cfb7f293f9f40a66ef352c0751e222a602f25c`).
The carrier reduction follows from the actual Weil class bijection and the
invariance of the numerical conditions.
