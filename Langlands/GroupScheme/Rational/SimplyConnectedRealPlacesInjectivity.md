# Reduction of real-place injectivity to the all-place Hasse principle

`SimplyConnectedRealPlacesInjectivityStatement` is the injectivity clause of
`SimplyConnectedRealPlacesCohomologyStatement` written using the Library's
`Cocycle.Cohomologous` relation. The reduction applies
`NumberFieldHassePrincipleStatement` to the simply connected group.

`SimplyConnectedRealToAllPlacesComparisonStatement` gives the local step
on its own. For two cocycles of a simply connected group on the same finite
field cover of a number field, cohomology at every real place implies
cohomology at every completion. The statement uses `Cocycle.LocallyCohomologous`
and permits any finite field extension, which is separable in characteristic
zero.

At a complex place the completion is isomorphic to the complex numbers and
therefore algebraically closed. The finite field extension embeds into the
completion over the number field. Adjunction gives a section of the pulled-back
cover, and evaluating a cocycle at that section produces its coboundary cochain.

At a finite place the completion is a nonarchimedean local field and the group
remains simply connected. A maximal ideal of the tensor product of the completion
with the finite field extension gives a finite separable residue field over the
completion. Its spectrum maps to the pulled-back cover and is fpqc over the
completion. The local vanishing theorem supplies a trivialization on that field
cover, which descends to the pulled-back cover by `Cocycle.IsTrivial.of_refine_fpqcCover`.
At either type of place, multiplying the first trivializing cochain by the
inverse of the second gives the required twist.

This internal reduction follows J. S. Milne, *Algebraic Groups* (2017), Theorem
25.65, p. 563, using Theorems 25.61(a) and 25.64, pp. 561–562. The all-place
Hasse principle is an explicit premise of the Lean theorem.
