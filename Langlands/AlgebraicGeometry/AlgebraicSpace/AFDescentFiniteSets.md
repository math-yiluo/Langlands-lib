# Finite-set AF descent conditional on quasi-affine-source AF descent

Author: Worker 133.

This internal module completes the reduction of the exact full AF-descent
proposition to the explicit mathematical premise
`FiniteSurjectiveQuasiAffineSourceAFStatement.{u}`. It does not prove that
premise and is not an unconditional proof of the task target.

## Compact neighborhoods in arbitrary schemes

In namespace
`Langlands.AlgebraicGeometry.AlgebraicSpace.AFDescentFiniteSets`,
`compactNeighborhood` chooses a compact open neighborhood of any finite
point set inside a specified scheme open containing it. The scheme need
not satisfy AF. The construction uses Mathlib's prespectral scheme
topology and `PrespectralSpace.exists_isCompact_and_isOpen_between`.
Empty finite sets and arbitrary underlying points are included.

## AF of any representing scheme

`hasFiniteAffineNeighborhoods_of_representation` starts with a finite
geometrically surjective map from an actual AF scheme `U` to a relatively
quasi-separated algebraic space `Y` over `Spec R`, for an arbitrary
commutative ring `R : Type u`. It takes an actual natural isomorphism from
the presheaf of an arbitrary representing scheme `P` to `Y.presheaf`,
and the explicit quasi-affine-source AF descent premise. It proves AF
of `P.left`.

The implemented proof transports the original map to an actual finite
scheme morphism `U → P` by full relative Yoneda. For a given finite set
`E` of points of `P`, its inverse image is finite, so AF of `U` supplies
one affine source open containing it. The complement of the finite
image of the source closed complement is an open of `P` containing `E`.
Choose a compact open `W` inside this open containing `E`; its entire
source inverse image still lies in the chosen affine source open.

The open scheme `W` gives a representable open subfunctor `A` of
`Y.presheaf`. Its representing compact scheme makes `A` quasi-compact.
The proof verifies `A ≤ universalAffineOpen π V` by the universal-image
adjunction: any section of the original source whose image factors
through `W` factors through the chosen affine source open. This is
checked using the transported actual finite scheme morphism and the
point-range factorization criterion.

`AFDescentOpenCharts.openAFModel` applies the explicit prerequisite to
produce an AF model of `A`. Relative Yoneda full faithfulness identifies
that model with `W`. Its composite open immersion into `P` has image
containing `E`. The preimage of `E` is finite because this immersion is
injective. An affine open containing that preimage in the AF model has
affine open image in `P`, containing `E`. This proves the existing AF
property with no restriction to closed points.

## Exact conditional reduction

`finiteAffineNeighborhoodsDescent_of_quasiAffineSourceAF` has conclusion
exactly
`FiniteSurjectiveFiniteAffineNeighborhoodsDescentStatement.{u}`, with
the sole explicit external mathematical premise
`FiniteSurjectiveQuasiAffineSourceAFStatement.{u}`.

It first invokes the conditional scheme gluing theorem
`AFDescentOpenCharts.exists_representation`, then proves AF of that
scheme using the preceding finite-set argument. The original commutative
base ring, actual source and target, finite and geometric-surjectivity
predicates, target qcqs premises, all finite point sets, and natural
isomorphism on all scheme tests are retained in the exact conclusion.
Every construction remains over the original base.

The independent unconditional proof of the quasi-affine-source theorem,
followed by the exact main theorem's proof validation, semantic review,
and publication, remains necessary. No approximation, normalization,
conductor, pushout, Picard or parent representability task is discharged
by this conditional reduction alone.
