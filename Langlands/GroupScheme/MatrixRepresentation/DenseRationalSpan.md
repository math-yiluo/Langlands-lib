# Matrix span from a dense rational-point monoid

`span_rationalMatrix_comp_eq_top_of_dense` takes an actual matrix representation of a reduced group scheme over an algebraically closed field, all-test irreducibility, and an explicit dense monoid family of rational points. It proves that the matrices of that family span the full matrix algebra. The field and the indexing monoid have independent universes; the coordinate index has the universe required by the existing actual matrix-representation interface. No characteristic assumption is imposed.

The implemented proof first uses `irreducible_rationalAction_comp` to transfer all-test irreducibility to the natural linear action of the dense family. This action agrees definitionally with `matrixAction` of the composed rational-matrix homomorphism. The Burnside matrix-span corollary then gives the result.

This is an internal composition of the dense-family stability construction and the irreducible-representation span proof. Reducedness, the specified density, and irreducibility are explicit premises. The result does not establish rational-point density, the existence of such irreducible representations, spectral boundedness, or the host compactness equivalence.
