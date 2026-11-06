# Finite separable local lifts through smooth surjections

This internal deduction combines published actual-scheme constructions.
It supplies local lifts for the quotient-point obstruction argument in the
local Kneser--Tits task. It uses no local-field arithmetic.

`Langlands.AlgebraicGeometry.FiniteSeparablePoint T` stores a field
`extension : Type u`, its field and `F`-algebra structures, finite
dimensionality and separability, and an actual morphism
`Spec extension → T` over `F`. Its field and extension properties are
available as instances. For a nonempty smooth `T`,
`finiteSeparablePointOfSmooth T` chooses such data using the existence
proof below.

For any field `F : Type u`,
`exists_finiteSeparable_point_of_smooth` proves that every nonempty smooth
scheme over `F` has a point with values in a finite separable extension
`L/F` with `L : Type u`. Smoothness means smoothness of its structure
morphism; the scheme need not be affine or quasi-compact.

Because `Spec F` has one point, a nonempty scheme over it has a surjective
structure map. The published `hasEtaleLocalSections_of_smooth` supplies an
étale surjection `E → Spec F` and a map from `E` to the original scheme.
The published `GaloisChartPoint.exists_separable_point` supplies a point of
`E` over a finite separable extension in the same universe. Composing the
two actual morphisms produces the required point.

`exists_finiteSeparable_quotient_lift` applies this to a smooth surjective
map `q : G.X → Q` over `Spec F`, where `G` is any actual group scheme and
`Q` is any scheme over `F`. For every base point `y : Spec F → Q`, it
produces a finite separable extension `L/F` and an actual point
`g : Spec L → G` with `q(g)` equal to the restriction of `y`. No quotient
universal property or group structure on `Q` is assumed.

The proof uses the published actual scheme fiber
`Dynamic.flagQuotientFiber G q y`. Its map to `Spec F` is smooth and
surjective by base change, hence the fiber is nonempty. Apply the first
lemma to this fiber and compose the resulting point with its map to `G`.
The fiber's defining equation gives the displayed local-lift equality.

`Langlands.GroupScheme.finiteSeparableQuotientLift G q y` chooses the
resulting data as a `FiniteSeparablePoint G.X` together with the proved
equation that its image under `q` is the restriction of `y`. Both chosen
constructions use classical choice on the proved existence statements;
they add no further geometric hypothesis.

The extension may depend on `y`. Neither lemma proves a lift over `F`.
They assert no cocycle vanishing, no existence or smoothness of an
unsupplied quotient, and no rational-point generation theorem.
