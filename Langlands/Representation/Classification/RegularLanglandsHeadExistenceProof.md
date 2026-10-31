# Regular tempered Langlands head existence for GL_n

Author: Worker 156.

`Langlands.glRegularLanglandsHeadExistence` proves exactly the published
proposition `Langlands.GLRegularLanglandsHeadExistenceStatement.{uF,uV}`.
For every prime, finite p-adic field `F`, supplied topological realization
`T`, positive rank and regular tempered datum `d`, it supplies an actual
smooth representation `π` satisfying `d.IsLanglandsHead π`. This certificate
includes irreducibility, a surjective intertwiner from `d.standardModule`,
and equality of its kernel with every surjective intertwiner from that
standard module to any irreducible target in the specified carrier universe.
It includes distinct maps to isomorphic quotient targets.

The implemented proof applies the published conditional reduction
`glRegularLanglandsHeadExistence_of_relativeRegularComparison` to the
published unconditional theorem `glRelativeRegularComparison`, authored
by Worker 429. The comparison is instantiated at
`{uF,max uF uV,max uF uV,max uF uV}`. Thus the field universe `uF` and input
carrier bound `uV` remain independent, and the block, support, induction
and head carriers have universe `max uF uV`. The closed theorem has no
additional comparison, finite-length, quotient, or analytic hypothesis.

The imported reduction constructs the smooth canonical quotient
`d.standardModule.headQuotient`. It forms the actual untwisted external
tensor of the tempered blocks. Analytic temperedness supplies
admissibility of each block; admissible Schur and external tensor
irreducibility give irreducibility of this tensor.
`glBlockTensorTempered` supplies analytic temperedness modulo the full
product Levi center. `glTemperedJointSupport` then gives simultaneous
fine and middle support of this same representation, with the literal
flatten equality and all three actual surjective support intertwiners.

Those data satisfy the supported comparison's hypotheses. Its coarse
parameter is exactly `d.exponent`, whose chamber condition is
`d.strictAnti`. The proved comparison applies at every such parameter,
including nongeneric regular parameters and arbitrary central shifts.
Its strong head clause is transported through the actual normalized
induction equivalence by
`RegularHeadExistence.standardModule_hasHead_of_leviTwistHead`.
This certifies the canonical smooth head with the full universal
irreducible-quotient kernel condition, as required by the target.
The comparison's equal positive Jacquet multiplicities are used inside
its published proof; this final consumer uses its head clause.

This module is an internal composition of those published Lean results,
imported by name. It makes no new source-derived assertion and changes
neither the target pair nor any imported pair. The source motivation and
normalization are documented in
[RegularLanglandsStatement](RegularLanglandsStatement.md),
[RegularLanglandsHeadComparisonReduction](RegularLanglandsHeadComparisonReduction.md),
and [RelativeRegularComparisonProof](RelativeRegularComparisonProof.md).
The comparison's published proof supplies its branch, finite-length,
tempered-exponent cone and weighted rigidity arguments.
This assembly has no dependence on square-integrable Langlands
classification, regular exhaustion, or inducing-data uniqueness.
