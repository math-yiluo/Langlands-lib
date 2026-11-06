# Complete binary Steinberg big-cell data

For any infinite field `k : Type u` of prime characteristic `p`,
`steinbergBigCellData p` constructs a `SteinbergBigCellData` bundle for the
actual binary special-linear group. Its witnesses are the rank-one integer
lattice, the actual inclusion of its diagonalizable group with entries
`diag(t⁻¹,t)`, the actual upper triangular subgroup, its inclusion, the
explicit Weyl point, the last-diagonal character coordinate, and the
bottom-right affine entry coordinate.

All seven laws are proved for these same witnesses. The first six are the
previously constructed same-character left and inverse right covariance,
identity normalization, coordinate nonzerodivisor property, global unit-entry
factorization, and diagonal lift of common triangular points. Both the
factorization and intersection lift hold on every relative scheme test,
including nonaffine and nonreduced tests, with factors and lifts on the
original test. The final law uses `cofinalCovariantBasis p e` at degrees
`p^e - 1`. These degrees are cofinal by `e < p^e`. The basis is of the entire
actual covariant coordinate space, and the previously proved comparison with
binary homogeneous substitution gives irreducibility of its actual Chevalley
regular representation in each such degree, including degree zero.

`exists_steinbergBigCellData` unpacks this explicit bundle. Its type is exactly
the existential conclusion of `SteinbergBigCellStatement` specialized to the
actual binary special-linear group. The proof applies the bundle's generic
unpacking lemma; no structural-existence premise is assumed.

This is a derived assembly of explicit matrix geometry, quotient regularity,
the full binary covariant-space comparison and proved binary polynomial
irreducibility. The geometry and regularity are by Worker 669; the actual
upper subgroup, covariant comparison, regular-action comparison and cofinal
adapter are by Worker 1369. The construction retains infinitude and prime
characteristic, so it applies in particular over the algebraically closed
fields of the general target. It proves the full existential conclusion for
this specific group without a simply-connectedness premise. The universal
`SteinbergBigCellStatement` for arbitrary simply connected groups remains a
separate unproved target.
