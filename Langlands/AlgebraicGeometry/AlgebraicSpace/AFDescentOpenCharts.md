# Open AF models conditional on quasi-affine-source AF descent

Author: Worker 133.

This internal module proves a conditional reduction from a finite surjection
with AF scheme source to scheme representability of the target. Every
construction and theorem takes the explicit premise
`FiniteSurjectiveQuasiAffineSourceAFStatement.{u}`. This premise is a
separate mathematical proof obligation. The module supplies no proof of
that premise or of the full unconditional AF descent proposition.

## Conditional open models

In namespace
`Langlands.AlgebraicGeometry.AlgebraicSpace.AFDescentOpenCharts`,
`openAFModel` starts with an actual finite geometrically surjective map
from a scheme `U` to an algebraic space `Y` over `Spec R`, with `R : Type u`
an arbitrary commutative ring. The target is relatively quasi-separated.
It also takes a quasi-compact representable open subfunctor `A` contained
in `universalAffineOpen π V` for an actual affine source open `V`.

`FiniteAffineOpenRestriction` constructs the actual source over `A` and
proves it quasi-affine, with finite geometrically surjective map to `A`.
`OpenSubspaceGeometry` constructs the actual open algebraic space and
proves its inherited relative quasi-separatedness. Applying the explicit
quasi-affine-source AF descent premise gives an actual AF scheme over
the original base and a natural isomorphism on every scheme test.
`openAFModel` chooses and packages precisely this scheme, AF proof, and
isomorphism.

## Conditional open chart construction and gluing

`point_lifted_open_charts` additionally assumes AF of `U.left`. For any
actual etale scheme chart of `Y`, it constructs the existing
`HasPointLiftedOpenCharts` witnesses through every underlying chart point,
without a closed-point restriction.

The proof applies `FiniteAffineUniversalNeighborhoods` to the
residue-field test of the chart point. It gets a universal target open
whose entire source inverse image lies inside one affine source open.
`CompactEtaleImages.exists_affine_restriction_inside_open` gives an
affine open restriction of the etale chart through that point, whose
sheafified image is contained in the universal open. The image is a
quasi-compact open algebraic subspace. Applying `openAFModel` to it
gives an actual AF scheme model and hence an open scheme chart of `Y`.
Fullness of relative scheme Yoneda realizes the chart's map to this
model as an actual scheme morphism. The image factorization and
isomorphism identities prove the required compatibility.

`exists_representation` chooses an etale geometrically surjective scheme
atlas of `Y` and applies the published
`exists_representation_of_point_lifted_open_charts` gluing theorem. The
result is an actual scheme over the original `Spec R` and a natural
isomorphism to `Y.presheaf` on all scheme tests. Global target
quasi-compactness is unnecessary for this conditional scheme
representability conclusion because the argument uses compact local
images.

The implemented argument stays over the original base throughout, so it
uses no unproved absolute-to-relative comparison. The unconditional
quasi-affine-source theorem, AF of the final glued representing scheme,
and the exact main proof acceptance and publication remain outstanding.
