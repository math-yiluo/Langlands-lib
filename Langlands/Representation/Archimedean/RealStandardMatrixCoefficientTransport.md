# Transport of real standard module matrix coefficients

`realStandardMatrixCoefficientTransport` proves
`RealStandardMatrixCoefficientTransportStatement` for the actual real
standard modules. The compact tests `φ` and `ψ` are continuous functions on
`O(n)` integrated against the same finite measure. If their integrals on
corresponding vectors agree at the identity, the two matrix coefficients
agree at every `g ∈ GL_n(ℝ)`.

The proof applies `RealReverseTransfer.matrixCoefficient_eq_of_rel` to the
graph of the intertwiner on the underlying principal-series functions.
The Library's signed-power formulas for the position characters and its
inclusions into compact-finite principal series give the hypotheses on the
two families. The compact intertwining equation keeps the graph stable
under orthogonal right translations, and the Lie intertwining equation
keeps it stable under right derivatives in real matrix directions. Every
pair in the graph comes from a source vector, so the assumed identity
comparison applies to it. The Library theorem gives the comparison at
each group element.

This internal consequence of the Library's compact and Lie models extends
identity evaluations of compatible matrix coefficient functionals to the
group integrals used in a trace comparison.
