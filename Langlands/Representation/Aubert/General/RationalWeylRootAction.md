# Actual relative Weyl action on the character lattice

This is an internal derived construction on the published character lattice and
the two existing relative Weyl quotients. It supplies the actual character action
needed to formulate the root-sign comparison in the general Aubert consumer.
It does not prove that comparison or construct a Coxeter system.

All declarations belong to
`Langlands.Aubert.General.RationalPointFamily`. The base is an arbitrary field
`k`, `T` is a commutative group scheme over `Spec k`, `G` is a group scheme, and
`i : T.toGrp ⟶ G` has monomorphic underlying scheme map.
`schemeWeylCharacterAction i` descends the published `GroupScheme.weylAction i`
to `relativeWeylGroup i`. The existing theorem
`centralizerPoints_subgroupOf_le_ker` proves that the full scheme-centralizer
denominator acts trivially on the character lattice, so `QuotientGroup.lift`
defines this action without any additional kernel hypothesis. Its formula on
the class of a normalizer point is proved by reflexivity.

`weylCharacterAction i hN hZ` acts on the same actual character lattice through
the actual quotient `Weyl i = N(torusPoints i)/Z(torusPoints i)`. It composes
the scheme quotient action with the inverse of the previously constructed
`weylEquiv i hN hZ`. Both exact comparison premises remain visible:
`hN` equates scheme-normalizing points with the normalizer of the literal
torus point image, and `hZ` equates scheme-centralizing points with its full
centralizer. Neither equality is proved by this module.

`weylCharacterAction_weylEquiv` records compatibility with that equivalence.
`weylCharacterAction_mk` computes the action of a scheme normalizer representative
viewed in the actual quotient. `weylCharacterAction_point_mk` gives the formula
for every normalizer of the actual torus point image, using the inverse of the
equality-induced normalizer equivalence. Thus the action uses the same ambient
normalizer points throughout. In the published normalizer action, if a point
normalizes `i` through a torus automorphism `σ`, the character `χ` is sent to
`σ.inv ≫ χ`; this inverse pullback convention is preserved.

With the additional hypothesis that `G` has affine structure morphism,
`schemeWeylCharacterAction_image_relativeRoots` and
`weylCharacterAction_image_relativeRoots` prove preservation of the exact
published `relativeRoots i` as a set. The first uses quotient induction and the
published preservation theorem for normalizer points; the second substitutes
the inverse ambient comparison. The membership equivalence
`weylCharacterAction_mem_relativeRoots_iff` then follows from injectivity of the
linear equivalence and equality of the root-set images.

The source motivation is Renard, *Représentations des groupes réductifs
p-adiques*, version of 9 July 2026, V.4.1 and V.4.6, printed pp.118 and 120–121
/ PDF pp.124 and 126–127. V.4.1 uses the full-centralizer Weyl quotient;
V.4.6 describes minimal representatives through actual root images and the
length-increase/positive-root comparison. Descending and transporting the
already published action between implementation models is an internal
derivation, not a separately numbered theorem attributed to Renard.

No finite instance, root-system realization, simple reflection identification,
positivity/length comparison, standard-Levi intersection, topology property,
classification input or representation-theoretic identity is asserted here.
In particular the action is on characters themselves, so a future comparison
can explicitly distinguish a root from its negative instead of using only
conjugacy of reflection labels.
