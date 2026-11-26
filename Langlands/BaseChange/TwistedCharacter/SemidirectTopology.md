# Topology of a semidirect product with discrete component group

`SemidirectProduct.productTopology` transports the product topology from
the underlying two coordinates, and `homeomorphProd` gives the coordinate
homeomorphism. Hausdorffness, local compactness and total disconnectedness
transport along this homeomorphism. When the index group is discrete, each
coordinate slice is open, including the canonical embedded subgroup.

For `isTopologicalGroup_of_continuous`, the action is jointly continuous
because its slices are continuous and the index is discrete. The
semidirect product's multiplication and inversion formulas in coordinates
are then continuous. The topology and the transported instances are scoped
to `SemidirectProduct`.

This is the product-space realization used for the rational points of the
cyclic extension in Arthur–Clozel, *Simple Algebras, Base Change, and the
Advanced Theory of the Trace Formula*, Chapter 1, §2.1, printed pp. 10–11.
Source ID `arthur-clozel-1989-base-change`, SHA-256
`c2e47ee562810367ebcacd3f1c242eda40b9e78b271668e36d99ce31001f9a19`.
The topology construction applies to any discrete index group with the
given continuity of its action.
