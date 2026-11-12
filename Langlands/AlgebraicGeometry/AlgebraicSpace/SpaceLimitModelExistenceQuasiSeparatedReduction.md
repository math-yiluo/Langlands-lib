# Reduction of space model existence to scheme-relation descent

Authors: Worker 116, with atlas naturality comparisons supplied by Worker 131.

This construction gives the full model-existence conclusion under the explicit
scheme-only assumption
`Langlands.AlgebraicGeometry.EtaleEquivalenceRelation.LimitModelExistence`.
That assumption remains unproved. This is a conditional reduction, not a proof
of the unconditional target `SpaceLimitModelExistenceQuasiSeparated`.

The initial lemmas turn an actual scheme pullback square into its isomorphism
in the slice category and prove naturality under a morphism of cartesian
squares. A cartesian morphism of étale equivalence relations over an object
base-change square supplies the relation base-change square by vertical
pasting. These are intrinsic categorical comparison lemmas using the actual
pullback universal properties.

`restrict_kernelPair` maps a represented kernel-pair square by restriction
of presheaves, then transports its three represented corners with the natural
scheme-Yoneda base change isomorphism.

`isoOfRelationComparison` uses cartesian comparisons on the actual source and
relation schemes. Naturality identifies the base-changed relation projections
with the original projections. The base-changed quotient atlas is étale and
surjective. Thus its kernel pair is the same represented relation as that of
the original space. The two fppf sheaves, viewed as étale sheaves, are
isomorphic by `commonEtaleKernelPairIso`. The result is an isomorphism of
algebraic spaces over the actual source base.

`Model D c Y` records a stage, its actual algebraic space, quasi-separatedness,
a quasi-compact locally finitely presented atlas, and the base-change
isomorphism. `model hRel` constructs the entire package:

1. The limit of the affine stage schemes is affine.
2. `FinitePresentationEtaleAtlas.presentation` constructs the original affine
   atlas and its finitely presented represented relation.
3. The explicit assumption `hRel` supplies the stage relation and actual
   cartesian comparison maps.
4. `FinitePresentationRelationQuotient.quotient` constructs its quasi-separated
   quotient with the required finite presentation atlas.
5. `isoOfRelationComparison` identifies its change of base with the original
   space.

`spaceLimitModelExistenceQuasiSeparated_of_relation` extracts the existential
conclusion from this package, retaining `hRel` as an explicit argument. Neither
construction assumes separatedness of the original algebraic space, and
neither weakens the original target's indexing or universe quantifiers.

Provenance: this is the presentation/quotient argument in the proof of Stacks
Project Lemma 70.7.1 (Tag 07SK), specialized to affine scheme bases and with
the unresolved scheme descent step made explicit. Registered source
`stacks-limit-morphism-review-2026-11-07`, directory SHA-256
`35f3718ed86ff158e3a8f3765940bd0a8e69861a3af500daf315ec210efe1663`,
file `07SK.html`, essential-surjectivity portion.
