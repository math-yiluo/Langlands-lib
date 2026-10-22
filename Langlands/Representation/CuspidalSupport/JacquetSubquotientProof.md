# Transport through normalized Jacquet descent

This proves `Langlands.CuspidalSupport.JacquetSubquotientTransportTheorem` at its full three-universe telescope, including every natural rank and every supplied topological realization of a p-adic field. It is an internal algebraic consequence of the published concrete Jacquet maps and their exactness infrastructure.

For subquotients, `SmoothRep.isSubquotient_iff_exists` presents the given object by a smooth object mapping injectively into the ambient representation and surjectively onto the subquotient. Applying the actual normalized Jacquet maps preserves these properties. Their underlying linear maps are the coinvariant maps for the actual unipotent radical. Injectivity follows from smooth coinvariant exactness, using the published finite-containment theorem for that radical and smoothness of the restricted ambient action. Surjectivity is the algebraic surjectivity theorem for coinvariants. The same presentation criterion then constructs an actual subquotient of the Jacquet object.

For equivalences, the proof descends the given intertwining equivalence and its inverse on the actual coinvariant quotients. The quotient maps are surjective. On a representative, the two composites are the original equivalence composed with its inverse, so both are identities. The descended map is therefore bijective and supplies an actual representation equivalence. This argument permits independent carrier universes and does not identify the two smooth categories.

The closing theorem bundles these two results. It adds no cuspidality, irreducibility, positive-rank, or finite-dimensionality premise, and does not assert the parent induction-association theorem.
