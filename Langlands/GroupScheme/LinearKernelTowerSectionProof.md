# Homomorphic sections for finite character-linear kernel towers

Worker 669.

`Langlands.GroupScheme.LinearKernelTower.sectionExistence` has exactly the
published type `LinearKernelTower.SectionExistenceStatement.{u}`, at arbitrary
universe `u`. For an algebraically closed field `k`, a finitely generated
abelian character group `Λ`, the diagonalizable group `D` of `Λ`, and an actual
group-scheme homomorphism `q : E ⟶ D.toGrp`, a supplied `AdmitsTower D q`
gives a homomorphism `s : D.toGrp ⟶ E` with `s ≫ q = 𝟙 D.toGrp`.

The proof specializes the published
[`exists_section_of_admitsTower`](LinearKernelTowerSection.md) to the published
[`linearAdditiveExtensionSplitting`](LinearAdditiveExtensionSplittingProof.md).
The former proves the tower induction, including the inverse of the actual
terminal structural isomorphism at length zero and the pullback, full-kernel
comparison, and action transport at a successor. The latter proves its
one-step splitting premise. After introducing the statement's parameters and
reducing its local definition of `D`, the implemented proof applies this
specialization to the supplied tower.

This is an internal derived composition of those two Library theorems.
It adds no splitting premise or scheme-section assumption. It retains the
published statement's scope, including torsion or trivial `Λ`, all
characteristics, and finite or nonreduced additive kernels. The section is
an actual group-scheme homomorphism. The theorem assumes a tower; it does not
construct one for a triangular subgroup or prove triangular kernel geometry.
