# Scalar defects of actual tensor-cube splitting charts

This module proves
`Langlands.CentralSimple.splittingChart_scalarDefect_cube_isCoboundary_of_tensorCube_split`.
Let `k → L` be an arbitrary extension of fields, `A` a `k`-algebra, and `I`
a nonempty finite matrix index type. For an actual splitting chart
`e : L ⊗[k] A ≃ₐ[L] Matrix I I L`, an actual ground-field matrix splitting
of `(A ⊗[k] A) ⊗[k] A` with index `(I × I) × I` supplies a scalar cochain
whose coboundary is the cube of the actual scalar defect attached to `e`.
The result has no Galoisness or finite-extension premise; those hypotheses
enter later when the cochain is used for descent.

The proof uses the actual tensor-product charts from
`TensorProductSplittingCharts`. Kronecker products of prescribed invertible
lifts induce the tensor-chart action on every matrix: the pure tensor
identity is extended by additive induction through the actual matrix tensor
algebra equivalence. The product of two actual lift defects is the defect
of their actual Kronecker lifts. Applying this twice gives the cube of the
original scalar defect.

To connect this prescribed lift family with the chosen lifts used to define
the tensor chart's scalar defect, the proof compares their actual matrix
conjugations. The published unit-scalar ambiguity theorem supplies pointwise
scalar comparisons. Normalizing a coboundary lift family gives an honest
one-cocycle, and scalar comparison then transfers its trivializing cochain.
An actual ground-field split presentation trivializes the chosen defect by
comparison with its canonical scalar-extended chart. These steps prove the
claimed cube coboundary without an assumed Brauer tensor compatibility law.

All comparisons are implemented directly from the supplied algebra
equivalences and published matrix innerness and scalar-ambiguity results.
This module does not assert nonsplitting of degree-six division tensor
cubes or perform the Sylow fixed-field descent; these are in
`CentralDivisionTensorCubeNonSplit` and `SylowTwoOddSplitting`.

The entry proposition `Langlands.CentralSimple.TensorCubeScalarDefectCoboundaryStatement` records the precise scope of
`splittingChart_scalarDefect_cube_isCoboundary_of_tensorCube_split`: its explicit hypotheses are universally quantified in a
Prop-valued definition. The implemented theorem and proof are retained.
This module is a statement module because its mathematical entry is
a proposition, rather than a data construction.
