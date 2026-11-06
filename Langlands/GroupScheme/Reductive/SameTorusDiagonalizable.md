# A diagonalizable presentation of the same opposite-parabolic intersection

This internal construction composes the published split diagonalizable
isomorphism with the all-test intersection theorem for opposite dynamic
parabolics. It supplies the diagonalizable map needed for the intersection
clause of the Steinberg big-cell target while preserving a supplied torus.
It is not a proof of existence of the structural data in that target.

Let `R : CommRingCat.{u}` and let `T` be a group scheme over `Spec R`.
A `SplitTorusDiagonalizableModel R T` consists of a type `I : Type u`,
finiteness of `I`, and an actual isomorphism `D(I → ℤ) ≅ T` over `Spec R`.
Here `D` is the existing diagonalizable group scheme of an additive group,
constructed from its group algebra. For a supplied `IsSplitTorus T`,
`IsSplitTorus.diagonalizableModel` chooses its finite split-torus
presentation `T ≅ Gm^I` and composes the published isomorphism
`D(I → ℤ) ≅ Gm^I` with the inverse of that presentation.
All objects remain over the original base and in the original universe.

For any supplied map `j : T → G`, the model's `embedding j` is its
isomorphism followed by `j`. The name refers to a presentation of the
supplied subgroup map; the construction itself imposes no monomorphism
hypothesis on `j`. The model's `pointLift` sends a point of `T` on an
arbitrary relative test scheme through the inverse isomorphism.
`pointLift_comp` proves equality of the resulting ambient points, using
the inverse-hom identity. Consequently `range_embedding` identifies
the full subgroup functors of this map and `j`, not just their rational
points.

For the intersection result, additionally suppose that the underlying
scheme of `G` is affine. Supply a cocharacter `coch`, representatives
`iP : P → G` and `iQ : Q → G` of its dynamic parabolic and opposite
dynamic parabolic, and the original `j` as a representative of its full
dynamic centralizer. If points of `P` and `Q` have equal images, the
published opposite-parabolic intersection theorem gives a point of this
same `T` with that image. Transport through `pointLift` gives a point of
`D(I → ℤ)` with exactly the same image under `embedding j`.
The relative test scheme is unrestricted, including nonaffine and
nonreduced schemes, and the point is global on that test scheme.

Neither the presentation nor its intersection theorem requires a field,
smoothness, reductivity or maximality of the supplied torus. No existence
of a torus, opposite-parabolic representatives, a regular cocharacter,
a conjugating point, a bi-covariant coordinate or a Steinberg
representation is asserted. Those remain obligations of the full
big-cell task.
