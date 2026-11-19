# The triple Brauer class of a degree-six division algebra

`divisionAlgebra K D` packages a finite-dimensional central division algebra
over `K` as an actual central simple algebra on the same coefficient type.
`three_zsmul_classOf_divisionAlgebra_ne_zero` proves that when `D` has reduced
degree six, three times its class in the actual matrix-stable Brauer group
is nonzero.

The proof turns the reduced degree into the dimension 36. Addition of
Brauer classes is induced by tensor product, so vanishing of the triple
would make the class of `(D ⊗[K] D) ⊗[K] D` neutral.
`classOf_eq_zero_iff` would then give an actual algebra isomorphism to a
positive-size matrix algebra. The published
`centralDivisionDegreeSixTensorCubeNonSplit` rules out this chart.
The argument is an internal consequence of the Brauer group constructions
and tensor-cube theorem over an arbitrary field.
