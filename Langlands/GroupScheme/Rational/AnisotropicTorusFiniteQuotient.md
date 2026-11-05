# Anisotropic torus extensions by finite group schemes

Author: Worker 1567.

This internal interface packages the algebraic input for the finite-component
step of the full scheme-center quotient compactness proof. It does not construct
the center quotient, identify its largest torus, or prove anisotropic compactness.

`HasAnisotropicTorusFiniteQuotient G` is a `Prop`-valued definition over an
arbitrary field in universe `u`. It asserts the existence of an actual torus
`T`, an actual closed subgroup homomorphism `j : T → G`, and
`IsAnisotropic T`, using the published split-rank-zero convention. It also
asserts the existence of an actual finite group scheme `Q` and an actual fppf
quotient `q : G → Q` by the full all-test range of `j`. Thus the finite quotient
retains component and nonreduced data. The definition contains no topology or
compactness premise. It requires a torus with finite quotient; it makes no
separate maximality assertion about that torus.

The imported theorem `IsTorus.isConnectedReductive_of_fieldSplitting` in
`Torus/ConnectedReductive` uses the field extension in the torus
predicate, the published connected reductivity of split tori, and reflection of
connected reductivity along that field extension. The extension interface's
`locallyOfFiniteType` theorem composes the quotient's locally finite presentation
with the finite target's structure morphism.

`HasAnisotropicTorusFiniteQuotient.compactSpace` is explicitly conditional on
`AnisotropicCompactnessStatement.{u}`. For an affine `G` over a nonarchimedean
local field, it applies that statement to the torus, using the preceding
connected-reductivity theorem. This gives compact torus points in precisely the
canonical `rationalPointTopology`. The finite-quotient compactness theorem then
gives compact points of `G` in their canonical topology. Only the attained
rational points in `Q` are used: the proof makes no rational-point surjectivity
claim for the fppf morphism. The algebraic interface supplies local finite type,
and no smoothness or connectedness condition is imposed on `G` or `Q`.

The content is derived infrastructure from the existing torus splitting,
field-extension reflection, fppf quotient, and finite-quotient point-compactness
APIs. Applying it to a reductive center modulo a split component still requires
an actual algebraic quotient, this purely algebraic finite-torus-extension
property for that quotient, the separately published anisotropic compactness
proposition to be proved, and the exact rational-lifting/topology bridge to the
literal center point quotient. This module proves none of those inputs.
