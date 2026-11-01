# Degree-zero scalar descent across a Laurent split

`LaurentSplitScalarDescentStatement.{u,v}` is a proposition about an arbitrary
family `D : I → RationalData K P`, where the field and index universes are
independent. It is the following conditional scalar descent assertion.

For every complete ultrametric normed field `K`, presented strict affinoid
algebra `P`, family `D`, and scalar function `f : P`, assume scalar descent for
the pullback of `D` to the actual upper Laurent quotient and to the actual
lower Laurent quotient. Assume that the pullback of `D` to the actual
upper/lower intersection quotient separates elements of that quotient. Then
`D` has scalar descent over `P`.

All three premises use `RationalData.pullback` along the actual base maps.
Compatibility in `ScalarCoverDescent` is equality of the actual ordered-pair
`interLeft` and `interRight` restrictions. Separation means joint injectivity
of the actual pullback base maps. The conclusion is unique lifting of
compatible scalar sections along the original actual quotient base maps.
There is no finite, point-covering, nonzero-base, reducedness, nonunit-function
or nonempty-locus assumption. In particular, an empty index type remains
allowed with exactly the stated premises.

The provenance is derived. This is the scalar degree-zero part of the
diagram-chase reduction in Piotr Achinger, *Introduction to non-Archimedean
Geometry*, November 22, 2020, Lemma 7.3.3 and its application on pp.66–67.
The source treats acyclicity of finite covers in broader degrees. This
interface retains only unique scalar descent, uses the existing explicit
unit-radius quotient presentations, and expresses the overlap hypothesis by
separation, the part needed for the degree-zero chase. The original is
registered as `achinger-2020-non-archimedean-geometry-nov22`, SHA256
`666cc6a90efbfc05f5fa0156044a259beaabdf989c45b633542e1cd2cdc0ec95`.

The intended proof uses the published unconditional `binaryLaurentGluing`
on `P` and on every original actual quotient. It must transport the given
sections through the proved bounded comparison squares, use the overlap
separation premise to make the two lifts compatible, glue them by binary
descent, and verify the original restrictions by binary separation after
base change. These steps are proof obligations, rather than assumptions
hidden in this statement.

This statement proves no standard-cover induction by itself, and claims no
higher Cech exactness, admissibility, finite-module descent or
arbitrary-radius result. It does not require nontrivial scalar valuation.
