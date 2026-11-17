# Differential generators of the actual affine section comparison

This is an internal continuation of `RelativeDifferentialsAffineSections`.
For a scheme morphism `f : X ⟶ S` and affine opens `U` and `V` with
`V ≤ f⁻¹(U)`, the earlier module constructs a canonical comparison between
actual differential sections on `V` and algebraic Kähler differentials of
the actual chart rings.

`relativeDifferentialsSectionsIso_D` proves that this comparison sends
the actual relative derivation section of a function `a : Γ(X,V)` to
the algebraic differential `d(a)`.
`relativeDifferentialsSectionsIso_inv_D` proves the inverse formula.
Neither result assumes smoothness.

The implemented proof uses the earlier factorization through the actual
affine Spec differential sheaf. `app_sectionPullbackLE_eq_adjoint`
first computes a morphism out of a pullback on a restricted pulled-back
section in terms of the restriction of its actual adjoint. It follows
from the pullback adjunction unit and naturality of the module morphism.

`affineChartSquareMap_fromSpec_D` applies that computation to the affine
differential square map. Its adjoint sends an actual differential to the
actual differential of the pulled-back function. Restriction of the
derivation to the top of the affine spectrum and the affine chart
function formula identify that function with the canonical global
section corresponding to `a`. The algebraic-to-Spec differential
comparison takes `d(a)` to this same section. The factorization and
injectivity of the comparison isomorphisms yield the asserted formula.

`moduleIso_inv_D_of_algebra_eq` records that the inverse-generator
formula survives transport along an equality of chart algebra structures.
Its proof is equality elimination; it is used to pass from `appLE` to
the actual group section algebra.

The provenance is these existing actual adjunction, differential, chart
and spectrum maps. No external source claim is added.
