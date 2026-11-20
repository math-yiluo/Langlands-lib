# Commutativity of regular semisimple centralizers

These auxiliary lemmas supply the ordinary centralizer calculations for
Henniart–Lemaire (2011), §§I.2.2 and I.2.4. They use the separable
characteristic polynomial in the Library's `IsRegularSemisimple`.

Over an algebraically closed field, Cayley–Hamilton and squarefreeness of
the characteristic polynomial imply semisimplicity. The eigenspaces span
the vector space, and the dimension of each is at most the root
multiplicity, hence at most one. Two endomorphisms commuting with the
original endomorphism preserve its eigenspaces. Each acts by a scalar on
a generator of an eigenspace, so the two composites agree there and
therefore on the whole space.

For a matrix over an arbitrary field, the proof applies this argument over
the algebraic closure and descends equality by injectivity of coefficient
extension. In particular the matrices underlying two elements of
`glCentralizer γ` commute when `γ` is regular semisimple. Over a finite
reduced algebra, `commute_of_commute_baseChange` applies the field result
in each residue field. The characteristic polynomial of the extended
matrix is still separable there by the characteristic polynomial map
formula and preservation of separability under field homomorphisms.
The residue field decomposition detects equality in the ambient general
linear group.
