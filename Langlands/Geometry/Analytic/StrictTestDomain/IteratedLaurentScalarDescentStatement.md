# Universal scalar descent for finite iterated Laurent covers

`IteratedLaurentScalarDescentStatement.{u}` states that the actual finite
family `iteratedLaurent g ε` has scalar descent after every bounded map from
its presented strict affinoid base to another presented strict affinoid
base. The field `K : Type u` is any complete ultrametric normed field. No
nontrivial-valuation assumption is imposed.

Here `g : Fin m → P` is arbitrary and `ε : Fin m → Bool` ranges over every
Boolean choice. In the imported construction, `false` means the upper
Laurent inequality and `true` the lower one. The family is recursively
constructed from the actual rational intersections and `whole`; no empty
leaf is removed. At `m = 0` its index is the singleton empty function type,
and its sole leaf is the actual whole-spectrum quotient.

`UniversalScalarCoverDescent` uses the literal actual
`RationalData.pullback` along each bounded base map. It requires unique scalar
lifting along the pulled-back structural maps for every section family
compatible under the actual ordered-pair intersection restrictions. It is
not merely a point-covering assertion. Zero and nonreduced bases, arbitrary
functions, and empty individual leaves remain allowed.

This is the scalar degree-zero specialization of the iterated Laurent
acyclicity in Achinger, *Introduction to non-Archimedean Geometry*, November
22, 2020, Corollary 7.1.2, p.65. The registered source is
`achinger-2020-non-archimedean-geometry-nov22`, SHA256
`666cc6a90efbfc05f5fa0156044a259beaabdf989c45b633542e1cd2cdc0ec95`.
The use of arbitrary complete ultrametric scalar fields is justified in the
intended proof by the published unconditional binary Laurent gluing theorem
and its quantification over every presented base. The literal base-change
formulation is an internal translation using the constructed leaf pullback
comparisons.

The statement asserts only unique scalar descent at the existing unit radii.
It does not assert higher Cech exactness, admissibility, finite-module descent,
standard rational descent, or any arbitrary-radius result.
