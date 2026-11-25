# Simultaneous torus diagonalization retaining a coordinate eigenline

This internal module, which supports the actual II.3.5 open-cell estimate,
retains a prescribed universal character vector in a full universal
character basis. It uses basis extension inside the union of the
character spaces, then assigns the prescribed character to the
retained basis vector.

`exists_characterBasis_containing` applies to any affine group's
representation whose universal character spaces span the entire
coefficient space. Given a nonzero vector in a specified character
space, it extends the singleton vector to a basis inside the union
of the character spaces using `Module.Basis.extendLe`. Reindexing
gives the original finite coordinate index. Choosing characters
for the other basis vectors and updating the retained index with
the specified character proves the exact prescribed-character
conclusion.

For a split torus preserving an actual coordinate line, one fixed
change of matrix coordinates simultaneously diagonalizes the torus
and retains the chosen line as a coordinate line. The exact subgroup
functor stabilizing the line is preserved on every scheme test.

More precisely, `exists_torusDiagonal_retaining_coordinateLine`
applies the character-basis theorem to the restriction through the
torus inclusion. The published
`coordinateLine_mem_characterSpace` supplies its chosen vector,
and the split-torus character decomposition supplies the spanning
hypothesis. The inverse of `basisCoordinateGL b` has the retained
original basis vector as the selected column, giving the
`IsCoordinateLineBasis` equation. The two rational-point matrix
comparison lemmas identify the corresponding conjugation with
the published universal character-basis diagonalization.

`HasExactCoordinateLineStabilizer.basisConjugate` uses the
published `basisConjugate_coordinateScalar_iff` for each unit
scalar on each scheme test. It preserves the exact original
subgroup functor, including its values on nonreduced test schemes;
it does not merely preserve the base-field point stabilizer.

`TorusEigenlineDiagonalization ρ i j` packages the basis matrix,
new line index, actual torus characters, retained-column equation,
and universal diagonal-character equation.
`torusEigenlineDiagonalization` chooses this data from the proved
existence result for a supplied split torus and preserved coordinate
line. Existence of a suitable diagonalization is a conclusion.

The construction is over any field, including positive characteristic,
and uses no highest-weight, irreducibility, reductivity, or analytic
input. The field universe is arbitrary, and the finite index type
need not be nonempty until the selected coordinate `j` supplies that
fact. This is an internal bridge built from the published character
and basis interfaces, rather than a translation of a named source
assertion. The quantitative torus weight gap required by II.3.5
is a separate result, proved in `ParabolicOrbitWeightGap`
(`exists_maximalParabolic_orbitPairing_gap`).
