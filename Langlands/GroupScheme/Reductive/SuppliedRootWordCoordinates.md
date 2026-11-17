# Full root word maps from supplied simple root parametrizations

This internal construction supports the independent Steinberg big-cell proof.
It assumes actual full parametrizations of the negative simple root functors
of a supplied split pinning. It does not assert their existence.

The first lemma transports a parametrization by a rational point normalizing
the torus. The normalizer conjugation equality for the actual relative root
functor identifies the image on every relative scheme test, including
nonreduced and nonaffine tests. The second lemma applies this transport
inductively to reflection words, using the supplied rational simple
reflection representatives and their character action.

These are derived transport lemmas. Their proof uses subgroup
representability and conjugation, not a theorem promoting a monic additive
map to a root parametrization through root dimension. In particular, it
does not use the existing `reflectionWordLoweringMaps_represents`,
`splitRootLieLine`, or the canonical choice of linked root maps.
