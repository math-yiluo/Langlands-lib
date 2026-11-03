# Actual real-to-adelic comparison for rational split tori

This module constructs the actual inclusion of real points of an affine group
scheme over the rationals into its full adelic point group, with identity point
at the finite places. For an affine commutative group scheme with a supplied
finite splitting, it identifies the image of the real identity component with
the existing intrinsic positive adelic subgroup and proves that the restricted
map is a closed embedding. This is derived internal infrastructure; it asserts
no new result from the automorphic literature.

## Actual coefficient and point maps

In `RationalRealAdelicPoints`, `infiniteRealAlgebraMap` is the rational algebra
homomorphism underlying the existing `PositiveRealIdeles.infiniteRealEmbedding
ℚ`. At each infinite place it uses the actual real embedding into the chosen
archimedean completion. The rational algebra structure follows from the
uniqueness of a rational algebra structure on these rings.

For an actual group scheme `G` over `Spec ℚ` with `IsAffine G.X.left`, `infinite
G` extends coefficients on actual affine points along this homomorphism. It is
a continuous group homomorphism for the existing regular-function evaluation
topologies. Continuity follows from continuity of the coefficient embedding and
the existing actual affine-point coefficient-map theorem.

`full G` composes `infinite G` with `AdelicGroupPoints.ofInfinite ℚ G`. In
particular, this is a map of actual group-scheme points, not a coordinate-defined
replacement for that map. The lemmas `infinite_full` and `finite_full` say that
its infinite projection is `infinite G` and its finite projection is the group
identity. The finite part is inserted on points; no ring homomorphism sending
every real number to the finite scalar one is asserted.

## Naturality of genuine splitting coordinates

`PositiveRealTorus.coordinates_affineMap` applies to a field `F`, an actual
commutative group scheme `T` over `Spec F`, a finite index type `I`, and a group
scheme isomorphism `e : T.toGrp ≅ splitTorus (Spec F) I`. For commutative
`F`-algebras `A`, `B` and `f : A →ₐ[F] B`, it states that the genuine coordinates
of `Lie.affineMap T.toGrp f x` are obtained by applying `Units.map
f.toMonoidHom` to the genuine coordinates of `x`. All types here lie in an
arbitrary common universe. This follows by expressing each coordinate as its
actual coordinate character and using coefficient naturality of character
evaluation. It requires no topology or affineness premise.

## Rational split-torus comparison

For the remaining results, `T` is an actual commutative group scheme over
`Spec ℚ` with `IsAffine T.toGrp.X.left`, `I : Type` is finite, and `e` is a
supplied actual splitting as above. The real and adelic coefficient types have
their usual topologies, and the actual point spaces have the existing
regular-function evaluation topology. No nonempty-index assumption is used;
rank zero is included. These rational specializations use universe zero.

`rationalRealFull_orderedCoefficientFull` proves, for every tuple `x : I →
ℝ≥0ˣ`, that extending the actual positive real point
`orderedCoefficientFull ℚ T ℝ I e x` with finite point one gives exactly
`PositiveRealTorus.full ℚ I T e x`, the existing scalar-idele coordinate
construction. The proof uses the actual infinite/finite point decomposition.
After applying genuine coordinates, coefficient naturality reduces both
projections to scalar identities: the real coefficient embedding agrees with
the infinite component of the scalar idele, and the finite component is one.
The proof uses explicitly typed projection homomorphisms, so it does not
replace the adele-ring algebra structures with unrelated product instances.

`realToAdelic T` restricts `RationalRealAdelicPoints.full T.toGrp` to
`orderedCoefficientPositiveSubgroup ℚ T ℝ`, the subgroup defined by positivity of
every actual rational character at the real point. It is bundled as a
continuous group homomorphism into the actual full adelic points. Its definition
uses no splitting. `realToAdelic_apply` records the underlying map, and
`realToAdelic_parameter` gives its value on the existing continuous positive
parameter equivalence. `realToAdelic_eq_full_parameters` gives the same formula
for an arbitrary intrinsic positive real point by recovering its parameters.

Under the supplied splitting, `range_realToAdelic` identifies its actual group
image with `intrinsicSubgroup ℚ T`. The latter consists of the actual adelic
points whose every rational character is a positive scalar idele. For the
forward inclusion, recover the positive parameters of a real point; for the
reverse inclusion, use the existing equality of the coordinate and intrinsic
adelic subgroups and insert the corresponding positive real point.

`isClosedEmbedding_realToAdelic` proves closedness and the induced-topology and
injectivity properties of this map. The parameter formula identifies it with
the existing closed embedding of positive scalar-idele tuples, composed with
the inverse positive real parameter homeomorphism.

Finally, `full_image_connectedComponent_one` states directly that the image of
the connected component of one in the actual real point group under
`RationalRealAdelicPoints.full T.toGrp` is exactly the underlying set of
`intrinsicSubgroup ℚ T`. The proof substitutes the previously constructed real
identity-component equality and uses the range equality just proved.

## Provenance and remaining scope

The construction uses the existing actual coefficient embeddings, affine-point
coefficient maps, point-product decomposition, split-torus coordinates, character
naturality, intrinsic positive subgroups, positive parameter equivalence, and
closed embedding of scalar-idele parameters. The final identity-component
comparison uses the corresponding complete ordered-field result at the actual
real numbers. The arguments above describe the implemented Lean proofs.

No restriction of scalars of an arbitrary number-field group is constructed
here. The module does not identify a greatest rational split central torus,
compare it with a maximal split torus over a general number field, or construct
an ambient central inclusion. It supplies the real-to-adelic comparison for a
supplied rational split torus. Unconditional reductive decomposition, measures,
reduction theory, finite volume and the remaining automorphic comparisons are
separate obligations.

The local topology instances have explicit names and expose exactly
`GroupScheme.affinePointsTopologicalSpace` on the actual affine-point
carriers. Their definitions and local scope are unchanged.
