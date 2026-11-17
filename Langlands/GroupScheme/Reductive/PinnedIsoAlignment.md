# Aligning a geometric isomorphism with two based root data

Worker 838. This is an internal prerequisite for the forward implication of
`InnerFormStarActionStatement`, derived from the published rational conjugacy of
maximal split tori, the root-datum comparison for torus-compatible isomorphisms,
and the Weyl correction of a root-datum equivalence. The geometric motivation is
Conrad, *Reductive group schemes* (2014), Lemma 7.1.1 and its proof, pp.238–239.

`SplitPinning.exists_inner_comp_based` takes split pinnings of two affine groups
over any field and an actual isomorphism between the groups. It postcomposes the
isomorphism by conjugation with a rational point of the target. The resulting
isomorphism carries the first chosen torus to the second through a specified
torus isomorphism. The resulting covariant root-datum equivalence has weight map
given by precomposition with the inverse torus isomorphism and preserves the
chosen bases. The assertion includes the actual torus inclusion square.

The proof first conjugates the image of the first maximal split torus to the
second, uses the inverse compatible group isomorphism to compare the actual root
data, and corrects that comparison by a Weyl element. The published equality
between the Weyl group image and rational normalizer action lifts the correction
to a second rational conjugating point. Multiplying the two points gives the
claimed inner postcomposition. No compatibility with the chosen root vectors is
claimed or needed.

`SplitPinning.InnerAlignmentStatement` is the Prop-valued definition of this
assertion, quantified over every actual isomorphism between the two supplied
split pinnings. `SplitPinning.innerAlignment` proves the proposition by applying
`exists_inner_comp_based` to each isomorphism.
