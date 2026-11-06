# Finite contragredient unramified-twist parameters

This internal helper isolates the finite-set part of
`SupercuspidalEqualRankLFactorStatement`. It defines
`IsContragredientTwistParameter F π σ a` using exactly the spectral parameter,
scalar character and smooth-contragredient equivalence in that statement.
The definition includes no assertion about a zeta integral or an L-factor.

The implemented finiteness proof works for any irreducible admissible pair
of the same positive rank, with independent field and representation universes.
An equivalence from a character twist of `π` to the smooth dual of `σ`
gives a bilinear form by evaluation. This form is nonzero because the equivalence
is injective and `π` is irreducible. Its simultaneous-translation factor is the
inverse of the twisting character. The published theorem
`centralBilinearVanishing` then places the reciprocal of the parameter in one
finite exceptional set. Filtering the inverses of that set gives precisely
the required finite set of twist parameters. Each parameter is nonzero by
the nonvanishing of complex exponentiation with nonzero base.

This is a derived implementation lemma: its mathematical inputs are the
Library's smooth-dual evaluation, scalar twists, finite generation of
irreducible group-algebra modules, and central bilinear spectral support.
It does not prove that these parameters are the poles, or that poles are
simple. Those analytic assertions are still needed for JPSS (8.1)(ii).
