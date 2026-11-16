# Representation by the finite affine parabolic quotient chart

This internal assembly works over `Spec R` for any commutative ring
`R : Type u`. It assumes a reductive group scheme `G`, a finite index type
`I : Type u`, actual relative parabolic inclusions `j a : P a ⟶ G`, and
`HasUniformParabolicFieldTypes j`. The last condition is a supplied
classification by a unique index over every field test. No existence of
such a family is asserted here.

`finiteAffineParabolicChart_locallySurjective` proves local surjectivity on
the actual big etale site of schemes over `Spec R`. For each point of an
arbitrary test scheme `T` and each actual parabolic family `F` on `T`, it
uses `etaleParabolicParameter` to choose an etale neighbourhood, a point
above the chosen point, an index, and a group-valued lift evaluating to the
restriction of `F`. Composing this lift with the chosen homogeneous
quotient projection and the component inclusion gives a section of the
actual scheme coproduct. The chart's group-lift formula identifies its
value with the restriction of `F`. These neighbourhood maps are jointly
surjective because a neighbourhood and point have been chosen for each
point of `T`. They therefore generate an etale covering sieve contained
in the image sieve of `F`. This also handles the empty test scheme.

`finiteAffineParabolicChart_isIso` regards the same chart as a morphism of
etale sheaves. Its source is the etale sheaf obtained from the represented
fppf sheaf of the actual finite quotient coproduct; its target is the
proved etale sheaf of actual parabolic families. Uniform field types
already imply that the chart is monic on arbitrary tests. Componentwise
injectivity gives local injectivity, and the preceding theorem gives local
surjectivity. The sheaf local-bijectivity criterion makes this morphism an
isomorphism. Forgetting to presheaves gives the asserted isomorphism of
the actual chart.

`finiteAffineParabolicIso` bundles that chart and its inverse.
`finiteAffineParabolicRepresentation` converts its lifted-Yoneda
isomorphism into `RepresentableBy`. The representing object is precisely
the previously constructed `finiteAffineParabolicQuotient`, whose
structure map is smooth and proper. Its functor of points includes all
scheme morphisms into the finite coproduct, including maps whose image
meets several components.

All arguments derive internally from the imported local-parameter,
uniform-field-type, quotient-family and sheaf results. No new translation
from literature is claimed. Existence of finite uniform types,
representation over arbitrary bases, and the unchanged unconditional
`RelativeParabolicSchemeStatement` remain separate obligations.
