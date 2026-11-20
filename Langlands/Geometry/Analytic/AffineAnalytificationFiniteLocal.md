# Affine analytification of finite local algebras

Let `D` be a finite-dimensional local algebra over a complete, nontrivially
normed ultrametric field `K`, and fix a finite polynomial presentation of `D`.
An analytic point is determined by its multiplicative seminorm on `D`. A
normed-field realization of that seminorm has prime kernel, which is the
maximal ideal because `D` is Artinian local. The resulting norm on the finite
residue field is the unique extension of the norm of `K`.
`subsingleton_space_of_finite_of_isLocalRing` proves uniqueness.
`nonempty_space_of_isLocalRing` uses the Library's maximal-center lift to
give existence even for a local algebra with just a finite polynomial presentation.

For a nonempty chart, `finiteLocalChartEquiv` identifies the original algebra
with the chart algebra by the coordinate map. The map is flat by the affine
chart comparison and faithfully flat because the chart spectrum is nonempty
and the source ring has only one prime. Its image is dense and is closed as
a finite-dimensional subspace over the complete field, giving surjectivity.

These deductions combine the Library's seminorm realization, chart flatness,
and chart density with uniqueness of the extended field norm. They retain the
nilpotent structure of the coordinate algebra on the chart.
