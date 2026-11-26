# Open mapping for genuine smooth carriers of Banach representations

`DerivativeSmoothVectors.isOpenMap_of_surjective_units` applies the Fréchet open
mapping theorem to genuine smooth vectors of jointly continuous Banach
representations of the units of a finite-dimensional real Banach algebra.
Any surjective continuous complex-linear map between these carriers is open in
the genuine word-derivative topologies.

The published basis-word embedding supplies metrizability, and the closed
range of the derivative coordinates supplies completeness for the additive
uniformity. For the target, the uniformity is the pullback of its neighborhood
filter at zero along subtraction. First countability makes this uniformity
countably generated. Completeness then gives complete metrizability and the
Baire property. The proof restricts scalars to the reals and applies
`Langlands.Analysis.frechetOpenMapping`.

This internal comparison supplies openness of smooth quotient maps for the
word-seminorm lift argument. Surjectivity is a hypothesis on the map.
