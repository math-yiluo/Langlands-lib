# Actual intersections of two full represented affinoid domains

Let `K` be any complete ultrametric normed field, `A` an actual presented
affinoid algebra over `K`, and `U,V : Domain K A` two full represented affinoid
domains. This internal construction gives an actual full domain `U.inter V`
whose locus is literally `U.locus ∩ V.locus`. Its algebra is the constructed
closed weighted Tate pushout quotient of the original bounded structural maps
`U.baseMap` and `V.baseMap`. Both projection arrows retain the original bounded
quotient legs. No rationality, strictness, nontrivial valuation, reducedness,
nonzero quotient, or nonempty-spectrum assumption is imposed.

## Compatible point realization

`AffinoidPushout.exists_point` applies to arbitrary bounded maps `f : A → B`
and `g : A → C`, not only domain structural maps. For points `x` of the actual
spectrum of `B` and `y` of the actual spectrum of `C` with equal images in the
spectrum of `A`, it constructs a point of the actual pushout quotient whose two
original projections are exactly `x` and `y`.

The proof uses the published `pointAmalgamation` theorem. It obtains a common
complete ultrametric normed field and actual bounded maps `α,β` realizing both
original point seminorms and agreeing over `A`. The constructed
`AffinoidPushout.lift` extends these maps through the actual closed quotient.
Pull back the norm point of that common field along this lift. Computing the two
original leg composites with `lift_comp_leftMap` and `lift_comp_rightMap` gives
exactly the original seminorm values on every element, so seminorm
extensionality proves the two point equalities.

This result is surjectivity onto compatible point pairs. It does not assert
injectivity of the comparison from a pushout spectrum for arbitrary bounded
maps.

## Full representation of the literal intersection

`Domain.represents_inter` proves that the original composite

`AffinoidPushout.leftMap U.baseMap V.baseMap` composed with `U.baseMap`

represents `U.locus ∩ V.locus` against every actual presented affinoid test. It
proves all three clauses of `Represents`.

First, the intersection is closed because both original loci are closed.
Second, the quotient spectrum has exactly that image. In one direction, both
original projection points belong to their represented loci, and the pushout
compatibility equation identifies their images in the original ambient
spectrum. Conversely, a point of the literal intersection lifts to an intrinsic
point of `U` and to an intrinsic point of `V` by their exact-image properties.
Their ambient images agree with the chosen point. The preceding compatible
point realization gives a point of the actual quotient, and its first projection
computes the required original ambient image.

Third, let any presented affinoid test `R` have a bounded map `φ : A → R` whose
spectrum image lies in both loci. The original full representation properties
factor `φ` uniquely as bounded maps from `U.algebra` and `V.algebra` to `R`.
Their composites with the original structural maps are both `φ`, so the actual
bounded pushout lift gives the required map from the constructed quotient to
`R`. The first leg identity proves that its structural composite is `φ`. For any
other such map, the original uniqueness statements determine both leg
composites; separation by both legs then determines the full map. Completeness
and ultrametricity of this target are supplied by the actual presented affinoid
construction over complete `K`.

## Constructed domain and pullback

`inter` stores this actual quotient algebra, the original first-leg structural
composite, the literal intersection, and the proved `Represents` property.
`inter_algebra` and `inter_locus` expose the chosen algebra and exact locus.
`interLeft` and `interRight` are actual arrows to `U` and `V`. Their restrictions
are exactly the first and second bounded quotient maps; the second structural
triangle is the proved pushout compatibility equation in reverse direction.

`interLift` takes any two actual domain inclusions from a third domain into
`U` and `V`. Their image containments put its locus in the literal intersection;
full affinoid-test factorization therefore constructs the required actual
inclusion into `U.inter V`. The two projection identities use the established
uniqueness of actual domain inclusions.

`interPullbackCone` uses both original quotient projections to form the cone
over any two actual arrows from `U` and `V` into a common containing full
domain. `interPullbackConeIsLimit` supplies each actual limit lift with
`interLift`; the projection and uniqueness identities follow from the existing
subsingleton property of actual domain inclusions. Thus this is a categorical
pullback in the existing full-domain category, with the constructed quotient as
its algebra and without an assumed intersection object.

## Provenance and scope

This is an internal derivation from the actual weighted affinoid pushout, the
published compatible-point field realization, and the existing full-domain
representation and inclusion APIs. It introduces no new original-literature
assertion or output assumption. The old and new algebras are actual quotient
algebras, and the proofs retain their complete bounded maps rather than
identifying algebra maps from their spectrum-point functions.

This module constructs intersections and their domain-category pullbacks. It
does not yet package a topological pullback cone on the two intrinsic spectra,
construct chart-independent restrictions in an unrestricted atlas, extend an
entire analytic atlas, or construct analytic and equivariant sites. Those are
further applications of the present actual intersection and the separate
bounded-map descent construction.
