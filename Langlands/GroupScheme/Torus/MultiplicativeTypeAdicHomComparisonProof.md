# Adic Hom comparison for isotrivial groups of multiplicative type

`Langlands.GroupScheme.multiplicativeTypeAdicHomComparison` proves
`MultiplicativeTypeAdicHomComparisonStatement.{u}` in every universe `u`.
For an adically complete noetherian ring, a source that becomes diagonalizable
over a finite étale surjective cover, and an affine target, restriction of
group-scheme homomorphisms to compatible systems on the adic thickenings is
bijective. The statement uses the Library's finite-type diagonalizable groups.
[Statement](MultiplicativeTypeAdicHomComparisonStatement.md)

The proof applies `multiplicativeTypeAdicHomDescent`, which reduces the
comparison to a source diagonalizable over the base itself. After introducing
the ring, ideal, and group schemes in the diagonalizable case, it applies
`HomScheme.AdicDiagonalizable.restrict_bijective_of_isDiagonalizable` to the
same ideal and group schemes. The two theorems use the same restriction map
`HomScheme.Adic.System.restrict`.
[Finite étale descent](MultiplicativeTypeAdicHomDescentProof.md) ·
[Diagonalizable comparison](../HomScheme/AdicDiagonalizable.md)

This is the split comparison followed by descent in SGA 3, Exposé IX,
Théorème 7.1, Gille–Polo recomposed edition, 2009, pp. 56–59
(original margins pp. 68–72). The registered source is
`sga3-expose-ix-gille-polo-2009`, SHA-256
`7c1e3d5b9d01ad01d0dd7b8b62045d012052e7890fb37adc3e7934ebb5fd6fc3`.
