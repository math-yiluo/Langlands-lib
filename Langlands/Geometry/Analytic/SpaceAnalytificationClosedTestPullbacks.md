# Affine and affinoid tests of closed immersions

Let `K` be a complete ultrametric nontrivially normed field, and let
`f : X' ⟶ X` be a morphism of separated algebraic spaces over `Spec K`
that are locally of finite type. Both spaces have supplied
analytifications. The analytic morphism `F` is compatible with `f` on
the two point families for every finite polynomial test.

For an affine test `Spec A ⟶ X` whose algebraic pullback is represented
by `Spec B`, choose finite polynomial presentations of `A` and `B`.
If the induced map from the analytification of `Spec B` to that of
`Spec A` is monic, `isPullback_of_affine_test` proves that the analytic
square is a pullback. To verify the universal property, take a
compatible analytic cone and pass to a chart cover on which its map
into the source analytification is defined by points over the chart
algebras. The other leg gives an algebra homomorphism from `A` to each
chart algebra. Injectivity of the affinoid point comparison converts
the cone equation into an equality of ring-valued points. The
algebraic pullback gives a lift on each chart, and chart gluing and
cancellation of the monic projection give the unique analytic lift.

For a presented affinoid algebra `R` and a point `x` of `X` over `R`,
the analytic base leg is `affinoidPointHom` applied to `x`. If `f` is
a closed immersion, the algebraic pullback over `x` gives a quotient
of `R` by an ideal. `PresentedAffinoidAlgebra.isClosed_ideal` gives
closedness of that ideal, and the proof forms the presented Banach
quotient. Bounded maps of `R` satisfying the cone equation annihilate
the ideal and factor through the bounded quotient map. The factor
agrees with the algebraic lift because both factor the same map
through the algebraic quotient. Surjectivity of the quotient map
gives analytic monicity by testing on chart spectra, and the same
gluing argument proves the pullback square.

`affinoidQuotientPullbackOfIsClosedImmersion` packages the ideal, its
closedness, and the two projections with their pullback property.
The construction is internal to the Library. It uses the algebraic
affine quotient pullback, the comparison on affinoid tests, and the
bounded universal property of the presented closed quotient.
