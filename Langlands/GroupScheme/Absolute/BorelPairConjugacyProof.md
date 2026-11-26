# Conjugacy of Borel pairs

`Langlands.GroupScheme.borelPairConjugacy` proves
`Langlands.GroupScheme.BorelPairConjugacyStatement.{u}`. For any two Borel
pairs of a smooth connected affine group scheme over an algebraically closed
field, it provides one rational point that conjugates both embeddings. The
witnesses include an isomorphism of Borel group schemes and an isomorphism of
commutative group schemes for the tori. [Formal statement](BorelPairConjugacyStatement.md)

The proof uses `borelConjugacy` to obtain a point `g` and an isomorphism
`φ : B ≅ B'` carrying the first Borel embedding to the second. Each torus in
a Borel pair factors through its Borel. The factorizations are maximal tori
of `B` and `B'` by `IsMaximalTorus.of_comp`, and `IsMaximalTorus.comp_iso`
transports the first one along `φ`. Smoothness and connectedness of `B'`
come from its Borel subgroup hypothesis, and its affineness follows from
its closed immersion into `G`. The proof applies `maximalTorusConjugacy`
inside `B'` to obtain a point `b` and the torus isomorphism.
[Borel conjugacy](BorelConjugacyProof.md), [maximal-torus conjugacy](MaximalTorusConjugacyProof.md)

By `innerIso_hom_comp`, conjugation by the image `bG` of `b` in `G` restricts
along `i'` to conjugation by `b` in `B'`. The product `bG * g` therefore
acts on the Borel embedding through `φ ≪≫ B'.innerIso b`. On the torus
embedding, the same product first transports the factorization along `φ`
and then applies the torus conjugacy equation inside `B'`. The two equations
use `innerIso_mul_hom` to express conjugation by the product.

The argument follows J. S. Milne, *Algebraic Groups* (2017), Proposition
17.13, printed p. 356 (PDF p. 372), in the direction of the formal
statement. The registered source `milne-2017-algebraic-groups` has SHA-256
`899b0f44f3c3ccfbaf5ed1cf9c180be7a8016b1c0e9709ca0c206304e5bd1cd0`.
