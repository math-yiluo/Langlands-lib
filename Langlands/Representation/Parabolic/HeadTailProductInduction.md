# Normalized product induction of the first factor and ordered tail

Author: Worker 111.

This internal construction specializes the published unconditional
`Langlands.Parabolic.orderedProductRegrouping` to the exact first/tail coordinates
in `Langlands.Group.GL.HeadTailBlocks`. Let `B` be an ordered shape of total rank
`n` with `h : B.length = k + 2`, and let `σ i` be bundled smooth complex
representations of its block groups. Both the first block and the remaining
`k + 1` blocks have positive total ranks.

`T.headTailProductFactors B h σ` is a two-factor family on the actual outer
shape `B.headTailShape h`. At label zero it is `σ (B.headIndex h)` with its
carrier raised by `ULift.{uF}`. At label one it is the actual normalized product
induction on `B.tailShape h` of `σ (B.tailIndex h j)`, retaining the original
order. The field universe `uF` and original carrier universe `uV` are independent.
Both outer factors have carrier universe `max uF uV`; the tail product already
has this universe and receives no further lift.

The two public `headTailRefinedFactors` lemmas identify the transported inner
families in the general regrouping statement. The head family is the canonical
rank-transported singleton family on the original first factor. The tail family
is exactly the original restricted family. The proofs use the published
head/tail label identities and proof irrelevance for the rank equalities.

`T.headTailProductInductionIso B h σ` is an isomorphism in the category of smooth
representations from the normalized product on `B` to the normalized product of
the displayed two outer factors. `T.headTailProductInductionEquiv B h σ` extracts
the corresponding actual complex-linear representation equivalence, with source
and target written as `T.normalizedProductInduced`.

The construction proceeds as follows:

1. The private inner family puts the canonical singleton family at zero and the
   original tail family at one. Function extensionality, the two public transport
   lemmas, and the two possible outer labels identify it with the raw transported
   family in ordered regrouping.
2. A second private family explicitly places the singleton product object at
   zero and the tail product object at one. Extensionality and cases on the outer
   label prove that it equals the products of the preceding inner families.
3. The singleton product is identified with the original head factor by the
   published `singleBlockTransportedProductEquiv`, then with its lifted carrier
   by `SmoothRep.universeLiftEquiv`. These give a categorical head isomorphism.
   The tail isomorphism is the identity. `CategoryTheory.Pi.isoMk` combines them.
4. A generic private adapter applies the first family equality under the inner
   induction functors, composes it with the second equality, and turns the result
   into an isomorphism with `eqToIso`. It composes with the preceding factor
   isomorphism, maps through the outer normalized product induction functor,
   and composes with the isomorphism chosen from the closed ordered regrouping
   theorem. Applying this adapter to the published head/tail coordinates yields
   the advertised categorical isomorphism.
5. `SmoothRep.equivOfIso` gives the final representation equivalence. The functor
   objects have the same actual normalized actions as `normalizedProductInduced`.

No evaluation formula for the chosen regrouping isomorphism is asserted. The
target acts on `GL_n` through the actual `B.headTailShape h`; there is no ambient
rank precomposition. Normalization and right translation come from the imported
product induction. Smoothness is supplied by the bundled input objects. No
irreducibility, admissibility, finite length, unitarity, Whittaker type, or
additional regrouping premise is required.

The provenance is internal specialization and composition of published ordered
regrouping, exact head/tail geometry, singleton evaluation, categorical family
transport, and carrier lift constructions. This module proves no analytic
Rankin–Selberg assertion, certified L-polynomial existence or product identity,
or literal heterogeneous three-block associativity theorem. Those remain
separate obligations of the parent L-factor task.
