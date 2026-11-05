# Proof of the joint-structure coefficient-growth implication

`rationalCoefficientModerateGrowthAssembly` proves the complete unapplied
`RationalCoefficientModerateGrowthAssemblyStatement.{u,uV}`.
The proof is internal and keeps its two structural premises explicit.

For the arbitrary connected reductive group in the conclusion,
`exists_maximalSplitTorus_genericCocharacter` chooses an actual maximal
split torus and generic integral cocharacter. The canonical affineness,
smoothness and rational-point topology instances are installed from the
target's data. `simpleRelativeRootFintypeOfIsSplitTorus` supplies the finite
simple-root enumeration using the actual Lie weight support.

Apply the joint structural premise to this torus and cocharacter. Keep its
factorization of the torus through the actual centralizer, its bijective
character comparison, its special compact properties, its standard-Levi
compatibility and its simultaneous standard basis. All these witnesses use
the same apartment `D`, vertex `x` and subgroup `D.specialCompactSubgroup x`.
`exists_isFiniteLatticeTransversal` extracts the needed finite transversal
from the standard-Levi comparison.

`rationalFiniteSignedCartanCover` uses the standard-cocharacter premise and
those same witnesses to give finitely many independent weakly positive
cocharacter charts. There is a fixed finite translate set; every rational
point is a product with the same special compact subgroup on both sides.
The signed chart directions include the entire root-pairing kernel.

Finally, `rationalFiniteChartModerateGrowth` applies to these charts, the
simultaneous standard basis, and the two compact outer sets. Their compactness
is the compact clause of the joint witness's `SpecialCompactProperties`.
Its conclusion is the rest of the exact coefficientwise proposition,
including every supplied closed matrix embedding, admissible smooth
representation, vector and smooth functional.

The field and carrier universes remain independent; the finite chart and
coordinate types both live at the field universe. No finite-length assumption
or restriction on characteristic, splitness or rank is introduced. This
proof establishes only the stated implication: it supplies no proof of
`StandardCocharacterStatement` or
`JointSpecialCompactBasisExistenceStatement`, and hence does not by itself
establish the unconditional coefficientwise growth theorem.
