# Openness of a torus centralizer in its normalizer over a field

Let a geometrically connected closed subgroup of an affine, locally finite-type group over a field represent the centralizer of a torus. If its normalizer is represented by a closed subgroup, the canonical inclusion into that normalizer is open. The factor lemma also applies to any closed normalizing subgroup through which the centralizer factors.

For a split torus, take the actual clopen identity component of the normalizing group. It is affine because the normalizing group is closed in the affine ambient group. Connected normalizer rigidity shows that this component centralizes the torus. The given centralizer is geometrically connected, so it lies inside the identity component. The two factorizations give an isomorphism with that component and hence an open immersion. For a torus over the original field, pass to a finite Galois splitting extension, transport the centralizer and normalizer conditions, and descend openness faithfully flatly.

This is the field comparison used with SGA 3, Exposé XV, Proposition 5.1(b), Remark 6.5 and the proof of Proposition 7.1(i). The Lean proof supplies the open immersion through connected normalizer rigidity.
