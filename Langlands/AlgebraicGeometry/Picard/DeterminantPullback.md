# Pullback of determinant line bundles from finite frames

This internal construction concerns an actual module sheaf `M` on a scheme
`X`, a family of open charts `T`, and actual finite free frames on those
charts. The frames all use the same finite basis index type. It derives the
pullback comparison from the published constructions of local free chart
pullback and of line bundles glued from unit cocycles.

`frameGenerator` expresses a frame vector on a smaller open as a local
morphism from the structure module. Evaluation on the unit gives the actual
section basis. Injectivity of that evaluation turns the basis expansion
into an equality of local sheaf maps. `pullbackFrames` uses
`chartFreePullbackIso` for the actual pulled-back module. The generator
formula for that chart and compatibility of local morphism pullback with
restriction give `frameGenerator_pullback`.

Applying local pullback to the generator expansion, using its scalar and
finite-sum laws, proves `matrix_pullback`: every transition coefficient is
carried by the actual structure-sheaf ring map to the coefficient of the
pulled-back frames. Determinants then give `unit_pullback` and
`cocycle_pullback`. The latter identifies the actual determinant cocycle
with `CocycleGluing.pullbackCocycle`.

When the charts cover `X`, `pullbackIso` composes the existing cocycle
pullback isomorphism with equality transport along that cocycle equality.
Its source is the actual sheaf pullback of the constructed determinant;
its target is the determinant constructed from the pulled-back frames.
`pullbackIso_hom_app_genSec` proves that it sends each pulled-back local
generator to the corresponding local generator of the target. The
full-subcategory lift `lineBundlePullbackIso` is the resulting isomorphism
of actual line bundles.

This module does not prove identity or composition coherence for these
pullback comparisons, their compatibility with changes of frames, or
variable-rank assembly. It does not construct the parabolic Lie determinant
or establish its ampleness. These remain separate obligations in the
polarized representability argument.
