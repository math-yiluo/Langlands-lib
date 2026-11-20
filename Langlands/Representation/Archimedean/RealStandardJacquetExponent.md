# The exponents of real standard module Jacquet functionals

`realStandardJacquetExponent` proves `RealStandardJacquetExponentStatement`.
For a nonzero Borel Jacquet functional on the actual `O(n)`-finite real
standard module of a list `ds`, the exponents after removing the
principal-series shift are a permutation of the position exponents of `ds`.
The proposition includes the signs in the hypothesis defining a Jacquet
functional. Its conclusion concerns the complex exponents.

This result is internal to the Library's real standard module model. The
proof uses the one-factor Gelfand calculation underlying the Library's
complex Jacquet exponent theorem. It transports the complexification of the
real matrix Lie algebra to the complex matrix Lie algebra and uses the
Gelfand operators of `VermaCentral`. For a Jacquet functional, upper
triangular matrix units with distinct row and column act by zero on
evaluation. The diagonal generators act by the Jacquet exponents. The
recursion `ComplexJacquetFinite.diag_pow` then evaluates each central
Gelfand operator as the corresponding sum of Gelfand polynomials.

Evaluation at the identity is a nonzero Jacquet functional whose exponents
at the positions `j : Fin n` are `b_j = t_j + (n-1)/2 - j`, where `t_j` is
the position exponent of `ds`. The derivative formula for the real
principal series and its transformation under sign matrices give the
eigenvalue relations. The common infinitesimal character forces the two
functionals to give the same Gelfand sums. For Jacquet exponents `a_j`, the
one-factor separation theorem `GelfandSeparation.exists_perm_of_gel_eq`
matches the coordinates `a_j + j` with `b_j + j` up to permutation.
Subtracting `(n-1)/2` gives the normalized Jacquet exponents on one side
and the position exponents on the other.

In `realStandardPositionExponent_perm_of_surjective`, the target module's
nontriviality makes evaluation at the identity a nonzero functional.
Surjectivity of the intertwiner keeps its pullback nonzero, and the compact
and Lie intertwining relations give the Jacquet equations on the source.
The theorem then matches the position exponents of the two lists up to
permutation.
