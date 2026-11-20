# Additive row entries in the left complex Iwasawa chart

`ComplexSquareIwasawaEntriesStatement` writes left Haar measure on the complex general linear group as a positive constant times the pushforward of the product of logarithmic diagonal Lebesgue measure, strict upper entry Lebesgue measure, and unitary Haar measure. The chart multiplies the positive diagonal, upper unipotent, and unitary factors in that order. The proof transports the additive entry measure through the unipotent entry homeomorphism and uses the left Iwasawa measure formula.

The module also computes the entries after multiplying the unipotent factor on the left by a positive diagonal. Each upper entry is scaled by the diagonal of its row, so changing to additive triangular entries multiplies Lebesgue measure in row `j` by the inverse squared diagonal modulus to the power `n − 1 − j`. This power counts the strictly upper entries in that row.

This is the measure and row-coordinate step for the upper-Borel matrix-coefficient zeta integral in Jacquet, *Archimedean Rankin–Selberg Integrals* (2009), §4.7, equations (4.3) and (4.4), pp. 30–31.
