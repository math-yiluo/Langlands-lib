# Character decomposition for arbitrary diagonalizable groups

Worker 537. Internal prerequisite for the representation theorem for groups of
multiplicative type, Task 7149.

The coefficient construction is defined for every commutative base ring `R`,
every abelian group `Λ`, and every finite matrix representation of the actual
group scheme `D(Λ)`. It does not assume finite generation or absence of torsion.
`universalMatrix` evaluates the representation at the identity of the representing
spectrum `Spec R[Λ]`; `coefficientColumn` extracts a column at a fixed exponent.

The translation identity from `Diagonalizable.Averaging` shows that each such
column satisfies its character equation after every coefficient extension.
Evaluation at the trivial character gives the identity matrix. Each standard
basis vector is consequently a finite sum of coefficient columns, proving that
they span.

Over every field, `affineUnitsEquiv_evalCharacter` identifies the coefficient
character with the existing actual character
`DiagonalizableCharacter.evalCharacter`. It compares global-section and affine
coordinates through `Corepresented.affineSectionsIso`.
`diagonalizable_coefficientColumn_mem_characterSpace` then places every column
in its all-algebra character space, and
`iSup_characterSpace_eq_top_diagonalizable` proves that these spaces span.
`iSup_characterSpace_eq_top_of_diagonalizable_iso` transports the result along a
supplied group-scheme isomorphism. Combining spanning with the published
`characterSpace_iSupIndep` gives
`isInternal_characterSpace_of_diagonalizable_iso`, the internal direct-sum
decomposition of the original vector space.

This is a coordinate implementation of the coefficient argument in Milne,
*Algebraic Groups* (2017), Theorem 12.12, printed pages 234–235 (PDF pages
250–251), registered source `milne-2017-algebraic-groups`, SHA-256
`899b0f44f3c3ccfbaf5ed1cf9c180be7a8016b1c0e9709ca0c206304e5bd1cd0`.
The proof generalizes the published split-torus construction in
`Dynamic.GeneralLinearCocharacterDiagonal` using group-algebra translation,
which also handles torsion in positive characteristic. Its extension to arbitrary
base rings is an internal algebraic generalization justified by the implemented
proof. The official 2017 errata snapshot of 2026-11-02 has no correction to
Theorem 12.12.

The main results have no smoothness, reducedness, finite-generation, or
characteristic hypotheses. The isomorphism form requires affineness of the
supplied group because the Library's `characterSpace` uses its coordinate
algebra. This unit establishes diagonalizable character decomposition; it does
not establish the Galois descent or orbit classification in Theorem 12.30.
