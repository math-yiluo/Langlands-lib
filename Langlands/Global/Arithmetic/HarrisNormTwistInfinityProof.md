# Infinity type and relative regularity under a Hecke norm twist

`Langlands.Global.Harris.normTwistInfinity` proves the unchanged
[`NormTwistInfinityStatement`](HarrisParityArithmeticTransportStatement.md)
for extensions `L/K` of totally complex number fields in any common field
universe. The proof needs neither CM nor Galois hypotheses.

For an infinite place `v` of `K` and a place `w` above it, the completion
extension has degree one because `v` is complex. The determinant norm of
the image of `x ∈ K_v` is `x^1 = x`. The completion map is surjective by
the same degree computation, so the local norm is its inverse. The proof
then uses the two `HarrisDatum` completion-embedding formulae: if the
chosen embedding of `w` restricts to the chosen embedding of `v`, the
complex coordinate of its norm is unchanged; if the conjugate embedding
of `w` restricts to the chosen embedding of `v`, that coordinate is
conjugated. Thus the modulus is unchanged in both cases, and the
conjugated coordinate swaps the two exponents of `complexCharacter`.

On the infinite ideles, `normComp` uses `infiniteAdeleNorm` on the
infinite factor and sends the finite factor `1` to `1`. Each lower
coordinate is the product of the local norms over its fibre. By
multiplicativity and `Fintype.prod_fiberwise`, the product of powered
moduli at the norm is the original product on `L`. The same reindexing
for the algebraic character gives the pullback of the lower type `t`,
namely `σ ↦ t (σ.comp (algebraMap K L))`. Distributing the power `a + b`
and applying `Harris.toCharacter_add` combines this pulled-back type
with the type of `ξ` to prove algebraicity after the summed twist.

For relative regularity, start with a separating unit in the common
lower completion `K_v`. By `ideleClassNorm_ofCompletion` and the degree-one
formula, the norm-twist factor at either upper place is `ν.infiniteComponent v`
evaluated at this same unit. Cancel this factor in `ℂˣ` (in particular, it
is nonzero). The original unit still separates the twisted components.
This clause does not assume that either character is algebraic.

## Provenance

This is a derived input for the Proposition 4.8 parity correction, not a
verbatim statement in [Harris 1998](https://arxiv.org/abs/math/9611226).
Definition 2.3 (printed p. 193) defines relative regularity, p. 195 gives
the half-integral normalization, and the proof of Proposition 4.8 (p. 202)
uses regularity under a Mackey norm pullback. Registered source
`harris-1998-local-langlands`, PDF pp. 17, 19, 26, SHA-256
`7934239ea37d0b91f741ae70c2ac157fe5d619cda4dd992ac24e39ae460c375b`.
