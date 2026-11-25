# The unique opposite Borel through a maximal torus

This module uses the Lie-containment proof `relativeParabolicLieContainment`
(`ParabolicLieContainmentProof`) and local-presentation helpers.

`relativeOppositeBorel` proves the unchanged
`Langlands.GroupScheme.RelativeOppositeBorelStatement` in every universe.
The base scheme is arbitrary. The group is reductive, the given relative torus
has its specified closed fibrewise maximal inclusion, and the original
relative Borel contains that torus on all test schemes. No additional
hypotheses are imposed.

The local dynamic presentation is constructed on an étale splitting cover of
the given torus, refined by point neighbourhoods. A regular fibre cocharacter
presenting the given Borel extends in the same split torus. Its positive
presentation and its torus-centralizer equality persist on a common open
neighbourhood. The regular-cocharacter criterion supplies an actual negative
relative Borel, and canonical pullback comparisons give all these data on the
direct pullbacks of the original group and torus.

The positive and negative dynamic parabolics intersect in the represented
centralizer, which is precisely the supplied torus. Over fields, opposite
Borels through that torus have equal images. The published Lie-containment
spreading proof promotes the residue-fibre comparisons to equality of
relative Borel images. In particular, the locally chosen negative Borels
agree on every overlap.

The all-test matching condition defines a global subgroup functor.
Its absolute membership sieve is closed for the fppf topology, and effective
closed-locus descent gives a closed scheme representative. Representability
transfer gives its group law and inclusion. The local Borel predicates
transport through the representative isomorphisms and descend along the
étale cover. The intersection equality also descends, since containment in
a monomorphically represented subgroup is detected on an étale cover.
The same relative uniqueness argument proves that every other opposite
Borel has the same all-test image.

The final theorem supplies `relativeParabolicLieContainment` to
`relativeOppositeBorel_of_lieContainment`. Its paired support modules explain
each reduction and the implemented proofs. This follows the local
construction, fibre uniqueness and descent route of Conrad,
*Reductive group schemes* (2014), Proposition 5.2.12, p.158; the implemented
route uses the independently proved local-presentation and Lie-spreading
interfaces. The target statement and all its original imported pairs are
unchanged.
