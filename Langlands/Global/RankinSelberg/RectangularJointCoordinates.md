# Joint leading-root and rectangular coordinates

This internal module defines `rectangularJointRow F b x` by concatenating
the adelic values of the leading-root tuple `b` with all entries of
`x`. The standard equivalence `Fin d × Fin a ≃ Fin (d*a)` enumerates
the rectangle.

A common archimedean norm bound for the leading-root row and the
rectangle bounds the joint row. The implemented proof checks the two
finite index blocks and uses the elementwise rectangle supremum norm.

For corrected roots, a two-sided correction norm bound `H ≥ 0`
gives an original leading-root row norm at most
`‖actual corrected root row‖*H²`. The proof applies the exact
leading-root inverse formula, projects multiplication to the mixed
archimedean ring, and uses submultiplicativity of its norm. The
correction term is a value of the diagonal tuple times a value of its
inverse, each bounded by `H`.

At finite places, suppose integral finite adele scalars `q` and `s`
give the common leading-root multiple `q*s²` and rectangular multiple
`s`. Then `q*s²` also clears the joint row. For the rectangular
entries the proof multiplies their known integral multiples by
`q*s`; for the leading entries it uses the supplied membership.

These are coordinate estimates and denominator implications, not a
Schwartz-majorant or Mellin-convergence assertion.
