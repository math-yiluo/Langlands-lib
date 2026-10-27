# Literal lifts and equivalences of normalized pairs

Author: Worker 645.

This is internal carrier transport infrastructure for the exact heterogeneous
three-block associativity consumer. It adds no representation-theoretic
hypothesis and does not prove associativity.

`literalULiftRepresentation_eq` identifies the target's literal conjugation by
`ULift.moduleEquiv.symm.conjRingEquiv.toMonoidHom` with the published pointwise
`universeLiftRepresentation`. `literalULiftEquiv` uses the actual complex-linear
map `up`, with inverse `down`; its intertwining identity is pointwise reflexivity.
The two evaluation laws state these maps explicitly.
`isSmooth_literalULift_iff` transfers the published smoothness equivalence through
the displayed identity of actions.

`Representation.Equiv.precomp` keeps an existing linear equivalence and evaluates
its intertwining identity on the image of a group homomorphism. It imposes no
continuity or smoothness conditions because it only compares actions.

`TopologicalData.normalizedPairInducedEquiv` applies the published
`normalizedProductInducedEquiv` to the two slots of `Shahidi.pairFamily` on the
literal `Shahidi.twoBlocks` shape. Its map acts on the values of the actual
smooth covariant functions through the tensor product of the two factor maps;
the inverse uses their inverses, as in `Induction.BlockEquivalence`. Source and
target carrier universes are independent, although each individual pair is a
family in a single universe.

The provenance is internal and derived: these adapters specialize
`Category.UniverseLift`, `Induction.BlockEquivalence`, and the existing ordered
pair definitions to the exact carrier expressions in
`ThreeBlockInductionAssociativityStatement`. No new external mathematical claim
or source translation is involved. The four universes of that final statement,
its four induction nodes, and its fixed total-rank transport remain separate
obligations of the consumer proof.
