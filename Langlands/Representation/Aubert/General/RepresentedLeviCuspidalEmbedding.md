# Cuspidal embeddings for an actual represented dynamic Levi

Author: Worker 1212.

This internal construction specializes the published cuspidal embedding
construction to a closed group-scheme representative of an actual dynamic
centralizer. Its inputs include a connected reductive group scheme `G` over a
nonarchimedean local field `F`, a cocharacter `χ`, and a closed morphism
`j : L ⟶ G` representing `Dynamic.centralizer χ`. Both schemes are supplied
with affineness for the rational-point topology. The ambient rational-point
group is assumed locally compact and nonarchimedean. Every point topology is
the canonical published `rationalPointTopology`.

`RepresentedLeviCuspidalEmbedding.cuspidalEmbedding` derives connected
reductivity of `L` from `dynamicCentralizerReductive`. It derives local
compactness of its point group from the closedness of the represented subgroup,
and transports the ambient nonarchimedean structure through the published
represented-point homeomorphism. The Hausdorff property follows from the
local-field point topology. These source properties are proved in the file;
they are not additional premises.

The construction retains the standard-family inputs of
`RationalPointFamily.cuspidalEmbeddingIndependentCarrier`: a maximal split
torus in `L`, a generic cocharacter, the standard-cocharacter,
standard-Levi-intersection and standard-endpoint statements, the relative root
system, closedness of the standard radicals and Levis, compactness of all
standard parabolic left quotients, and compact-subgroup containment for all
standard radicals. These structural and analytic statements remain hypotheses.

Write `e : L(F) ≃ₜ* Z(χ)(F)` for the published represented-point equivalence,
where the right side is the literal dynamic subgroup of `G(F)`. Given an
irreducible smooth complex representation `A` of that literal subgroup, the
result chooses a standard index `I` in `L`, an irreducible smooth complex
representation `σ` of its actual standard Levi, and an injective intertwiner
from `A` into the pullback along `e.symm` of the standard normalized induction
of `σ`. The chosen coefficient satisfies `IsLeviCuspidal` for the same source
standard family. This is a dependent pair of actual objects, a linear map and
the associated proofs. The normalized induction is the published
full-parabolic Haar-half-character functor.

The field universe `u` and the original carrier universe `uV` are independent.
The original carrier is retained. Only the chosen coefficient and its induced
representation have carrier universe `max (u + 1) uV`, as required by the
published independent-carrier embedding construction.

For the implemented proof, first pull `A` back along `e`; irreducibility is
preserved by the group equivalence. Apply
`cuspidalEmbeddingIndependentCarrier` to this representation of `L(F)`.
Keep its chosen index, coefficient and underlying injective linear map. For
an element `z` of the literal ambient Levi, specialize the existing
equivariance identity at `e.symm z` and use `e (e.symm z) = z`. This gives the
required equivariance after transport back, with the same injectivity proof.

The provenance is derived infrastructure from the published connected
reductivity, rational-point transport and cuspidal embedding results, rather
than a separate assertion from the literature. The construction proves no
finite-length result and does not identify source-standard cuspidality with
an ambient dynamic cuspidality predicate. The structural hypotheses, those
comparisons and the supercuspidal induction finite-length theorem remain
obligations of the full Renard VI.6.2 proof.
