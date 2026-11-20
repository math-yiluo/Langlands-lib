# Evaluation and precomposition for Cartier characters under base change

For commutative group schemes over a base \(S\), the comparison between
composite and iterated pullback is natural in the group-scheme
homomorphism. `charactersBaseChangeIso_precompose` uses that naturality
to compare precomposition of relative characters with precomposition
by the pulled-back homomorphism.

`evaluation_relativeHomBaseChangeEquiv` compares evaluation on the
original and extended tests. A test point is lifted to its section of
the relative group scheme. The composite and iterated lifts agree
under the canonical pullback comparison, as checked using the
projections. Conjugation by that comparison therefore gives the same
evaluation after projecting along the base map.

For relative characters, the canonical identification of the pulled
back multiplicative group with the new multiplicative group identifies
the output with the same global unit. These are internal coherence
laws for the actual relative Hom and character functors.
