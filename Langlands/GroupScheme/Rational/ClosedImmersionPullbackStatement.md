# Closed immersions and actual equivariant weight quotients

`PointedCoordinateWeights.ClosedImmersionPullbackStatement` is a
proposition uniform in every universe `u`, field `k`, split torus `S`,
and affine schemes `V` and `W` equipped with actual pointed `S`-actions.
For every pointed equivariant closed immersion `f : V → W`, it asserts
surjectivity of the actual coordinate pullback and augmentation pullback,
equality between each weight space on `V` and the image of the same
weight space on `W`, weightwise lifting of augmentation eigenfunctions,
and containment of the augmentation support of `V` in that of `W`.
All field characteristics and nonreduced affine schemes are retained.

This is a derived source target for the equivariant quotient arguments
in Conrad–Gabber–Prasad, *Pseudo-reductive Groups*, second edition (2015),
§3.3, printed pp.107–108 (PDF pp.133–134), including the equivariant quotient step in
Example 3.3.2 and the closed-subscheme comparisons in Lemma 3.3.4; the
registered source is
`conrad-gabber-prasad-2015-pseudo-reductive`. The extension to arbitrary
pointed affine schemes retains the actual morphism, its specified action,
and its fixed point. It imposes no group structure on either scheme.
Weights use `f(s.v) = χ(s) f(v)` on every commutative coefficient algebra.
The support records nonzero augmentation eigenfunctions and inserts no
zero character.

The file defines this target and proves none of its clauses. Coordinate
surjectivity is the geometric closed-immersion quotient fact; weightwise
surjectivity also needs the split-torus decomposition argument. In
particular, ordinary surjectivity does not itself supply weightwise lifts.
A focused proof successor must establish both for these actual
coordinates, using fixed-point preservation to obtain the augmentation
quotient. The final support containment then follows from the already
proved `support_subset_of_weightwise_lifts`.
