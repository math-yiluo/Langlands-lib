# Characteristic coefficients and polynomial centralizers for division units

Let `F` be a field and `D` a finite-dimensional central division algebra over `F`, of
reduced degree `d`. `divisionCoefficients F D a` assigns to `a : Dˣ` the coefficients
of its reduced characteristic polynomial in degrees `0` through `d - 1`.
`polynomialOfCoefficients_divisionCoefficients` reconstructs the polynomial using its
monic term of degree `d`. For a regular division unit `a`,
`corresponds_iff_coefficients_eq` identifies the matching relation with equality
of the coefficient lists for `a` and the matrix unit.

`reducedCharpoly_unit_conj` transports conjugation to the splitting matrix, where
conjugation preserves characteristic polynomials. `continuous_divisionCoefficients`
uses the continuity of the ordinary matrix coefficients and descends each coefficient
by a continuous `F`-linear retraction of the splitting field onto `F`. The continuity
lemma assumes the `F`-module topology on `D` and a topological field multiplication
and addition on `F`.

In `exists_sum_pow_of_commute_regular_division`, the separable reduced
characteristic polynomial becomes the separable characteristic polynomial of a
matrix in the splitting chart. Its cyclic basis expresses any commuting matrix
as a linear combination of powers below degree `d`. The linear retraction on the
first tensor factor descends that expression to `D`.

The coefficient parameter and polynomial centralizer are the ones used in Badulescu,
*Correspondance de Jacquet–Langlands pour les corps locaux de caractéristique non nulle*
(2002), §6, printed pp. 745–746, `badulescu-2002-jl-char-p`
(registered folder SHA-256 `dc96cc7848166e83a1f23478a1e341928ea8565bc9b649ffe84e452f3a205028`,
published PDF SHA-256 `638e7134bb13c9c718ee7e5c2c9f06634637598c6ba8cd465345baf1234ed370`).
