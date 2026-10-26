# Proof of the polynomial-module conjugacy bridge

The proof restricts the given polynomial-linear equivalence to scalars in the
field, using `Module.AEval'.of` to identify its source and target with the
original coordinate vector space. Polynomial linearity at `X` gives the
intertwining equation. The matrices of this linear equivalence and its inverse
form a unit `g`; the intertwining equation is `g * x = y * g`.
Right multiplication by the inverse gives `g * x * g⁻¹ = y`.

This implements the internal proposition `Langlands.MatrixAEvalConjugacyStatement`
over the same arbitrary field and universe, with no additional hypotheses.
