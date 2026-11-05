# Centrality of a radical under a Levi retraction

This internal derived unit concerns a specified solvable radical and an actual
rational Levi. It assumes neither a torus structure nor an ambient maximal-torus
condition.

`RationalLeviRadicalCentralityStatement` says that each rational Levi inclusion
`l : L → P` and solvable radical `r : R → P` admit a homomorphism `q : P → L`
with `l ≫ q = 𝟙 L` and central `r ≫ q`. The theorem
`rationalLeviRadicalCentrality` proves it using the actual Levi retraction
constructed from the multiplication isomorphism in the rational-Levi predicate.

The helper `IsSolvableGroupScheme.isCentral_comp_split` forms the schematic image
of `r ≫ q`. Published image geometry gives a smooth connected affine closed
subgroup with surjective projection. Surjectivity carries solvability to the
image. Normality follows from the published split-retraction image lemma. The
arbitrary-field normal-solvable centrality theorem then makes the image central
in the reductive group. Composing with the projection proves the conclusion on
all relative test schemes.

`IsRationalLeviSubgroup.isCentral_of_factor_solvableRadical` applies this result
to any subgroup with factors into both the given radical and the Levi. The
retraction identifies its Levi factor with the composite through the central
radical image, so that Levi factor is central.

The provenance is the indicated formal composition of Library image geometry,
solvable-image transport, split normality, actual Levi retraction, and the
arbitrary-field normal-solvable centrality helper. This unit does not assert
existence of a Levi or of a maximal torus.
