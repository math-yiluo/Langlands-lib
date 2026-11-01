# Actual lower quotient Fourier geometry

This internal development constructs the change of variables underlying JPSS
(1983), Section 4.8(4), printed p.415, on the actual lower quotients of
Section 4.7(1), printed pp.412–413. Its uniform quotient and determinant-slice
formulation is derived packaging of that matrix change of variables.

The reversed block rotation is the inverse original rotation; inverse transpose
fixes these permutation matrices and long Weyl conjugation inverts them.
Consequently the two rotations cancel through the dual change of variables.

The standard quotient homeomorphism is the quotient automorphism of
`g ↦ w * inverseTranspose(g) * w`, followed by right translation by `w`.
Conjugating by the two published `lowerToStandardHomeomorph` maps defines
`lowerDuality`. Both representative formulas are `g ↦ w * inverseTranspose(g)`.
The same construction works over every commutative topological ring.

For every canonical p-adic field the determinant of the Weyl matrix has order
zero, and inverse transpose negates determinant order. Quotient induction gives
both order laws. The image and preimage laws for the published determinant
slices follow from those order laws and bijectivity. There are no measure or
integrability assertions in this helper.

The registered original is `jpss-1983-rankin-selberg`, Jacquet,
Piatetski-Shapiro and Shalika, *Rankin–Selberg convolutions* (1983),
`/home/taskhub/central-library/Jacquet-Piatetski-Shapiro-Shalika--Rankin-Selberg Convolutions--1983.pdf`,
SHA-256 `d9feed6388ca5acf02ecc6a8cce984871a7c28f062ff441e45a71fa2d8962245`.
The source scan on printed pp.412–415 (one-based PDF pp.47–50) was
visually read. A bounded filename search of current Library and project
notes found no registered JPSS erratum. The separate equation (8) for
first-block integration belongs to Section 4.9, printed p.418;
Section 4.7 contains (1)–(5).

The Lean proof uses the published block-coordinate permutation formulas,
including `reversePermutation_symm_index_eq_rev`, to prove the rotation
identities, and `reflectedUnipotent` to descend the continuous group
automorphism. The two canonical order proofs use quotient induction.
Their field universe is arbitrary and independent of any representation
carrier; no representation is required. All the results retain block
sizes one. No new measure or representation hypotheses are introduced.
