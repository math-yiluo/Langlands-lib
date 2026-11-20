# Hilbert closure invariance from restricted coefficients

`preservesImageClosure_of_coefficients` uses joint-finite smooth lifts
whose values are the actual Hilbert orbit coefficients. It considers one
local unit group and assumes that restriction of the lifts preserves
analyticity and intertwines directional differentiation with the indicated
inserted Lie generators. The source subspace must be stable under those
generators. A supplied family meets every connected component, and its
action on the source image preserves that image. In the real and complex
matrix cases, `exists_unitary_point_mem_connectedComponent` expresses the
Library's component coverage using the standard compact groups.

For a vector orthogonal to the source image, the restricted lifts for all
vectors in the subspace vanish at the representative. Differentiation
in the direction \(gX\) gives another member of this same family.
The analytic componentwise vanishing lemma extends the vanishing to
the whole component. The Hilbert annihilator criterion puts every
translate of an original vector in the closure. Boundedness of the
action operator then preserves the closure. This internal lemma
applies the existing analyticity, differential and Hilbert
annihilator results to the same coefficient lifts.
