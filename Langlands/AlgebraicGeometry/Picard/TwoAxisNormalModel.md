# Normal finite-ring models of two-axis-trivial generic bundles

This internal construction composes the published abelian-scheme subalgebra
descent and the finite fraction-field model of an actual bundle with two
trivial restrictions. Normal finite-type subalgebra existence remains an
explicit hypothesis. The construction makes no extension claim.

`TwoAxisNormalModel A D` stores a finitely generated, integrally closed,
noetherian integer subalgebra `T` of the domain `R`. It includes an actual
abelian scheme over `Spec T` and a specified pullback square from `A` that
respects the units. It also includes an actual map from the generic abelian
scheme over the chosen fraction field `K` to the canonical generic base
change of the model to `FractionRing T`. Both projections are specified,
its square over `stageFractionFieldMap R K T` is cartesian, and its unit
compatibility is stated explicitly. An actual line bundle on that generic
model's self-product is trivial on both actual unit axes. Pullback along the
actual induced self-product map recovers `D` by a module-sheaf isomorphism.

`exists_twoAxisNormalModel` assumes integral closedness of `R` and
`NormalFiniteTypeSubalgebraStatement`. The two assumptions on `D` are
precisely triviality along the actual first and second unit axes. For every
finite subset of `R`, the theorem produces such a model with that subset
contained in `T`. All rings and schemes are in arbitrary common universe
`u`; no rank or noetherian hypothesis on `R` is imposed.

The proof first descends `A` to an abelian scheme over a finitely generated
integer subalgebra `C`. The chosen generic projection, followed by the
model comparison, gives a cartesian square respecting units. The cartesian
self-product theorem and its axis identities specialize the general
fraction-field two-comparison model to the actual generic product and
axes. This supplies a normal finite stage `T` and a bundle on the base
change of the model's product to `FractionRing T`.

Base change of the abelian model from `C` to `T`, and then to its canonical
fraction field, gives actual abelian schemes. Pullback cancellation and
universal properties construct the total and generic comparison maps,
including their projections, cartesian squares and unit equations. The
self-product cartesian square identifies the canonical generic model's
actual self-product with the base change of the original product. Its
projection equations and the axis identities transport the two trivial
restrictions to this self-product. Pullback composition transports the
bundle itself and its recovery isomorphism. Thus the final generic bundle
and both axes are actual Library objects, with no quotient-class substitute.

The two preliminary `twoAxisFirst_over` and `twoAxisSecond_over` lemmas
express that the actual unit axes are morphisms over the ground scheme;
they follow from the defining pullback lifts and the unit equation.

The provenance is a composition of Library theorems and Mathlib pullback
universal properties, with no new literature translation. Normal-stage
existence is not proved, no triviality witness is required to descend, and
no bundle on the total model or original self-product is produced. In
particular the valuation-ring two-axis extension statement remains a
separate proof obligation.
