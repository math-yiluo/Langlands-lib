# Single-block and rank-one tempered standard modules

Author: Worker 1737.

This internal prerequisite identifies the actual standard module with any of
its irreducible quotients when the tempered Langlands datum has one block.
It then proves that every datum of total rank one satisfies that condition.
The field universe `uF` and block-carrier universe `uV` are independent.
The topological data `T` are arbitrary supplied data on the p-adic field.

All declarations are in
`Langlands.PadicField.TopologicalData.TemperedLanglandsDatum`.

`standardModule_irreducible_of_length_eq_one` applies the published
`singleBlockNormalizedProductEquiv` to the actual determinant-twisted block.
That equivalence evaluates normalized induction from the full parabolic and
identifies its singleton tensor factor. Its target is the sole twisted block,
pulled back along the explicit rank-reindexing group equivalence. Character
twists preserve irreducibility, and pullback by a group equivalence preserves
irreducibility. The datum's block-irreducibility proof therefore establishes
irreducibility of the standard module.

`nonempty_standardModule_equiv_of_length_eq_one` unpacks the existing
`IsLanglandsQuotient` relation into an irreducible target and an actual
surjective intertwiner. The target has a nontrivial carrier, so this
intertwiner is nonzero. Irreducibility of the source makes it injective.
Together with the given surjectivity this constructs an actual complex-linear
equivariant equivalence.

`shape_length_eq_one` uses the bound that the number of positive blocks is at
most the total rank. A coordinate of the rank-one ambient space belongs to a
block, so at least one block exists. The two bounds give exactly one block.
`standardModule_irreducible_rankOne` and
`nonempty_standardModule_equiv_rankOne` specialize the preceding proofs.

`standardModuleEquivOfLengthEqOne` uses classical choice to select an actual
equivariant complex-linear equivalence from the proved nonempty type.
`standardModuleEquivRankOne` specializes this construction to total rank one.
These definitions supply maps, with inverses and equivariance, that can be
composed with other representation equivalences in subsequent comparisons.
No particular quotient map is designated as canonical.

The provenance is internal composition of the published actual induction
equivalence, twist-invariance and group-pullback results, and Mathlib's
irreducible-representation form of Schur's lemma. No literature result or
classification statement is assumed beyond those proved dependencies.
In particular the proof does not use analytic temperedness: block
irreducibility suffices for this conclusion.

These lemmas do not prove a spherical classification or any local-factor
formula. They remove the need for a separate rank-one standard-module
comparison in the spherical standard L-polynomial task. The higher-rank
standard-module comparison and Euler-product computation remain separate
obligations.
