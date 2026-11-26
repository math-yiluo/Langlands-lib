# Polarizations obtained by doubling divisors of a polarization

`polarizationDoublingDivision` proves the published
`PolarizationDoublingDivisionStatement`. For a positive integer `k`, an
actual homomorphism `mu` with `k • mu` a polarization has `2 • mu` a
polarization for the same dual witnesses. The proof works over every base
scheme and in every universe in the statement.

The isogeny assertion starts with `k • mu`, which is the composite of
`mu` with multiplication by `k` on either side. Nonzero multiplication
on an abelian scheme is an isogeny. The composite on the target side
gives finiteness of `mu` by cancellation past a separated morphism.
The composite on the source side gives surjectivity of `mu` and
faithfully flat descent of flatness. Composing with multiplication by
two gives the isogeny of `2 • mu`.

At a geometric point use the field extension in the given polarization's
actual ample Mumford presentation. The canonical dual comparisons carry
the original homomorphism and its multiples to this field. On that same
field the diagonal Poincaré bundle for `k • mu` is ample by
`ampleMumfordDiagonal`. Multiplicativity in the dual variable makes its
class the `k`-th power of the diagonal bundle class for `mu`.
`LineBundle.IsAmple.of_positive_tensorPower_iso` makes the latter bundle
ample.

With the usual normalization at the unit, the Mumford homomorphism of
the diagonal bundle for `mu` becomes `2 • (k • mu)` after multiplication
by `k`. This follows from `mumfordSchemeMapOfLineBundle_eq_pow_of_isoClass`
and `polarizationDiagonalMumford` applied to the pulled-back `k • mu`.
Multiplication by `k` is injective on abelian-scheme homomorphisms by
precomposition with the multiplication isogeny. Thus the ample diagonal
bundle supplies the field presentation of `2 • mu` with the same
extension. This checks the exact geometric polarization predicate.

Mumford, Fogarty and Kirwan, *Geometric Invariant Theory*, third edition,
Proposition 6.10 proves the diagonal Mumford identity for a polarization.
The argument here applies that identity at `k • mu` and uses the tensor
power comparison and cancellation to get the identity at `mu`.

Source `mumford-fogarty-kirwan-1994-git-3rd`, SHA-256
`25b78ea299e007fbabefb23e9dd7d30beba86c5c1eaa9718b8cc3f98f54932b2`,
Proposition 6.10, printed p. 121 (PDF p. 134).
