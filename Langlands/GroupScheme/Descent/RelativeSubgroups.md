# Effective descent of relative Borels and maximal tori

This internal construction uses the published effective descent theorem for
all-test invariant closed subgroups and the relative Borel and torus reflection
lemmas. Both effective descent constructors require the base schemes `S`, `U`
and the total ambient scheme `G.X.left` to be affine. Over the affine base `S`,
the last condition is equivalent to requiring an affine ambient structure
morphism. No solution or downstairs subgroup is assumed as input.

`RelativeBorelDescentData` contains an actual affine closed relative Borel in
the downstairs ambient group, an actual pullback isomorphism to the prescribed
upstairs source and the equation recovering the prescribed inclusion.
`IsRelativeBorelSubgroup.descentOfOverlap` constructs this data for an affine
ambient group under a flat surjective morphism between affine bases.
The original inclusion must be closed
and relative Borel, and its all-test overlap range must be invariant under the
canonical ambient descent isomorphism. Effective closed-subgroup descent
constructs the source, inclusion and recovery isomorphism. Source-isomorphism
transport gives the relative Borel property upstairs, and fpqc reflection gives
it downstairs. A morphism between affine schemes is quasi-compact, as needed
for this reflection.

`RelativeTorusDescentData` records the analogous actual commutative torus, its
closed inclusion, fibrewise maximality and exact recovery.
`RelativeTorus.IsTorus.descentOfOverlap` constructs it for an affine ambient
group under an étale surjective morphism between affine bases.
Inputs are a closed inclusion of a supplied
relative torus, fibrewise maximality and invariant all-test overlap range.
Effective closed-subgroup descent first constructs an ordinary group scheme.
The recovery isomorphism transfers commutativity upstairs; faithfully flat
quasi-compact reflection of commutativity equips the descended group with its
actual commutative structure. Étale reflection of the relative-torus property
and surjective reflection of fibrewise maximality prove the required properties.

The nonempty-existence lemmas implement the constructions; the two
`descentOfOverlap` definitions select the resulting data using classical choice.
These results descend supplied invariant subgroups. They do not construct
overlap invariance or a quasi-split inner form.

`RelativeTorusDescentData.range_le` proves that containment of the original
torus in the original Borel descends to their selected downstairs presentations.
Fpqc reflection of represented subgroup containment reduces this to the
upstairs containment; the recovery equations and invariance of ranges under
source isomorphisms give the required comparison.
`RelativeBorelDescentData.quasiSplit` uses the constructed Borel to witness
relative quasi-splitness when the downstairs ambient group is reductive.
