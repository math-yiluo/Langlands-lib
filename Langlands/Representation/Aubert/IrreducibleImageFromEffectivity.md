# Irreducible Aubert images assuming common-sign effectivity

Authors: Worker 76 (Aubert-specific assembly), using Worker 585's actual
fixed-factor-vector adapter and the published helpers described below.

This internal module reduces the existing `IrreducibleImageStatement` to
the explicit `SignedEffectivityStatement`. The latter remains a hypothesis
of `irreducibleImage_of_signedEffectivity`; this module does not establish
the unconditional target.

`normalizedInducedFiniteLengthObject` packages actual normalized induction
of a finite-length Levi representation as an actual finite-length object,
using the existing finite-length preservation theorem.
`alternatingOperator_injective` applies published all-rank involutivity to
an arbitrary exact Grothendieck class and uses injectivity of an involution.

For the conditional theorem, rank zero is the published identity case.
In positive rank, the published quasicuspidal embedding theorem embeds the
given actual irreducible representation into normalized induction of actual
irreducible quasicuspidal Levi data. It is applied with representation
universe `max uF uV`, so both the original representation and the eventual
output retain the prescribed saturated carrier universe.

Write `M` for the induced finite-length object and
`s = (-1)^(n - B.length)`. The published quasicuspidal eigenvalue theorem
gives `D[M] = s[M]`, where `D` is the existing unadjusted Aubert operator on
the exact finite-length Grothendieck group. Since `s` is either `1` or `-1`,
the sign-adjusted endomorphism `s • D` fixes `[M]`. The signed-effectivity
hypothesis gives effectivity of its image on every actual irreducible
subquotient of `M`, with this same sign.

The actual embedding specialization in `ActualFixedFactorVector` now applies:
injectivity comes from involutivity, the fixed class is the class just
constructed, and signed effectivity is supplied directly by the hypothesis.
That adapter uses actual composition multiplicities and integral counting
to obtain a single irreducible generator, realizes it by an actual smooth
irreducible representation, and removes the sign. Thus the original
operator sends the original actual class to the realized class or its
negative, with both finite-length witnesses obtained from irreducibility.

The provenance is internal assembly of the imported published results.
All Grothendieck groups retain the existing actual exact relations,
including nonsplit short exact sequences. The proof constructs no duality
complex and proves no positivity or homology assertion. It uses no
classification, admissibility, central-character or finite-dimensionality
premise. Independent field and carrier universes and all ranks are retained;
the target statement and every pair it imports are unchanged.
