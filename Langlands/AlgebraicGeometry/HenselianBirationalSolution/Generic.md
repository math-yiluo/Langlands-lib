# Generic points and agreement of morphisms

The underlying-set equivalence in `mem_genericPoints_iff_scheme` identifies
the generic points of irreducible components with the points without proper
generizations. Every point specializes from one of these. Generalizing maps
preserve this condition, in particular open immersions and flat morphisms.
The defining condition of `FibreGenerizationDense` puts every generic point
in a fibrewise dense set.

`ext_of_genericPoints_subset` reduces equality into a separated scheme to
agreement on an open containing the generic points of a reduced source.
`exists_extension_of_pieces` uses this test on local pieces presented by open
immersions. This is used to implement the dense comparisons of partially
defined products in BLR, *Néron Models*, §5.3 Lemmas 1–2, p. 120.
