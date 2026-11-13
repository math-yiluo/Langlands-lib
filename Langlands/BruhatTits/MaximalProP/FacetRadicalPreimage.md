# Radical preimages for the actual incident facet morphisms

This internal unit proves the third clause of `FacetReductiveComparisons`
and assembles all three clauses under `D.SatisfiesGroupAxioms`, at arbitrary
universe `u`. The models, radical representatives, quotients, schematic
images and maps are exactly those supplied by the original datum. In the
third clause the radical of the image can be any supplied representative
satisfying `IsUnipotentRadical`.

`incidentRadicalPreimageSubgroup` constructs the literal lower-parahoric
preimage of this radical's residue-field points, mapped into the original
generic rational-point group. Its subtype property records the proved
equality with the upper facet's original positive subgroup. The constructor
does not replace either subgroup by an abstract isomorphic group.

For incident facets `Fa` preceding `Fb`, write `A` for the upper neutral
special fibre, `B` for the lower neutral special fibre, and `f : A → B` for
the supplied special-fibre map. Let `q : B → Q` be the lower supplied
radical quotient and `p : A → I` the canonical projection to the actual
schematic image of `f` followed by `q`.

First, `HasSmoothConnectedUnipotentKernel.schematicImage_comp` proves
that `p` has smooth connected unipotent actual kernel. Factor `f` through
its parabolic schematic image. The first projection is fppf and has
the same actual kernel as `f`, by cancellation of the monomorphic image
inclusion. The lower radical lies in that parabolic, so the actual kernel
of the restricted quotient is represented by this radical, using the
factor and kernel comparison proved in `ParabolicUnipotentKernel`.
Compose these kernel properties and cancel the final monomorphic image
inclusion. `facetReductiveImageProjection_kernel` applies this result to
the actual supplied facet data and their general morphism and parabolic
image axioms.

Second, `HasSmoothConnectedUnipotentKernel.rationalPoints_surjective`
proves that an fppf homomorphism between affine groups over a finite field,
with smooth connected actual kernel, is surjective on rational points.
The actual kernel inclusion represents the full kernel functor.
The published finite-field torsor-point theorem, applied through
`HomogeneousQuotient.rational_lifts_of_finite_torsor_identity`, then
provides a rational lift. Unipotence is retained in the input predicate,
although this lifting argument needs only its smoothness and connectedness.

Third, the published `radical_comap_eq` applied to `p` identifies the
full inverse image of any supplied radical of `I` with the upper neutral
fibre's supplied radical, on every relative test scheme. Evaluating at the
identity test scheme gives the needed equivalence of radical membership
for residue-field points.

To prove the subgroup equality, take a lower parahoric point reducing into
the radical of `I`. Lift its radical point through `p` and then through the
upper neutral model's reduction. The all-test radical equality shows that
this lifted integral section is upper positive. Naturality and the
schematic-image factorization show that the quotient of the original
lower section by its lifted section reduces to the identity in `Q`.
The proved kernel formula for reductive reduction makes this quotient
lower positive. The supplied positive-radical clause includes the lower
positive subgroup in the upper one, so their product is upper positive.
Conversely, an upper positive section maps to a lower integral section;
reduction naturality and the same radical equality give its radical-image
preimage membership.

`facetReductiveComparisons` combines this equality with
`facetQuotient_isTorus_iff_isChamber` and
`reductiveImage_isGeometricBorel_iff_isChamber`.
`facetReductiveComparisonStatement` has exactly the type of the published
`FacetReductiveComparisonStatement`. The proof uses only the single-group
axioms and proved structural results, with no premise assuming the
comparison itself or global validity. Its provenance is internal
composition of those Library results. The full corrected maximal pro-p
proposition still requires its other structural inputs.
