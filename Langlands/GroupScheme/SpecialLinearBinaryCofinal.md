# Cofinal irreducibility for the actual binary covariant spaces

Let `k : Type u` be an infinite field of prime characteristic `p`. The
construction `cofinalCovariantBasis p e` is the existing full covariant
monomial basis in degree `p^e - 1`, indexed by `Fin (p^e - 1 + 1)`. It is a
basis of the entire actual coordinate subspace for the upper subgroup of
`SL₂` with weight `characterCoordinate k ^ (p^e - 1)`.

The theorem `cofinal_covariantRegularRepresentation_isIrreducible` gives
exactly the final clause of `SteinbergBigCellStatement` for this subgroup and
character. For each lower bound `e`, choose `e' = p^e - 1`. Since a prime is
greater than one, `e < p^e`, hence `e ≤ e'`. Choose the displayed basis. Its
actual Chevalley finite regular representation is definitionally the
representation constructed in `SpecialLinearBinaryRegularAction`, whose
rational-point irreducibility in every Steinberg degree has already been
proved. Degree zero, arising at `e = 0`, is included.

This is a derived adapter using the full actual-space basis and proved
regular-action irreducibility. It retains the infinitude premise of that
theorem; in particular it applies to algebraically closed fields of positive
characteristic. It does not supply the geometric witnesses or establish the
general big-cell statement.
