# Fractions for an invertible rational denominator

Author: Worker 36.

`Langlands.Analytic.RationalIdentity.fractions` takes an actual unit `g` of a
presented strict affinoid algebra `P` and a finite tuple `f` of elements of
`P`. It returns the tuple whose entry is `g⁻¹ * f i`, computed in `P`.
No completeness assumption is needed for this definition. The empty tuple
and the zero quotient algebra are allowed.

This is an internal algebraic construction for rational equations
`g * Y_i = f_i`. An actual unit is input, rather than an inverse inferred
from a spectral condition. The construction supplies neither a bounded
monomial estimate nor an equivalence of algebras; those belong to the
separate statement and proof.

The source context is Berkovich, *Non-archimedean analytic spaces* (Trieste,
2009), Definition 2.2.1 and Exercise 2.2.2(ii), printed/PDF page 9.
The source uses relative series and general radii. Here we reuse the
constructed unit-radius enlarged Tate quotient; identification with the
relative-series quotient is a separate obligation.

Registered original: `berkovich-2009-trieste-analytic-spaces`, content SHA256
`8cfe4f6f35d5e717ac67c5c8f5ef9ff9185f460bbe5f9a10aeacd84cddeeb2ca`.
Original URL: https://www.wisdom.weizmann.ac.il/~vova/Trieste_2009.pdf.
