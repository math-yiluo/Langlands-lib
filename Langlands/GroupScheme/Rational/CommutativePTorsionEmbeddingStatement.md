# Smooth commutative p-torsion groups embed in vector groups

`Langlands.GroupScheme.RelativeRoot.SmoothCommutativePTorsionVectorEmbeddingStatement`
is the embedding assertion of Conrad–Gabber–Prasad, *Pseudo-reductive Groups*,
second edition (2015), Lemma B.1.10, printed pp.565–566 (one-based PDF
pp.591–592). The registered source is
`conrad-gabber-prasad-2015-pseudo-reductive`, content SHA256
`1b77af44c90211db9a3efa50896a3722f4fd2df332b7ce2ec52202eb243e7f54`.

For every field `k` of prime characteristic `p`, a smooth commutative affine
actual `k`-group scheme `G` killed by `p` admits an actual closed group-scheme
inclusion into a finite-dimensional vector group over `k`. The torsion
condition is `HasUniformPowerExponent G.toGrp p`: it holds for every point
on every relative scheme test, including nonreduced tests. The vector-group
conclusion is `RelativeRoot.IsVectorGroup`, so the target's points on all
relative scheme tests have finite-dimensional additive coordinates natural
under arbitrary test-scheme maps.

There is no connectedness, unipotence, perfectness, infinitude or algebraic
closedness premise. In particular this is not the assertion that `G` itself
is a vector group over an imperfect field. The source also proves an étale
isogeny onto a vector group and an algebraically closed connected
classification; those additional assertions are outside this focused target.

The module defines a proposition and supplies no proof. Its intended use is
the arbitrary-field embedding step in CGP B.1.11–B.1.12 and B.2.5. A proof
must construct the ground-field embedding; an algebraically closed
classification alone does not establish it.
