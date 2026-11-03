# The actual Jacquet adapter conditional on standard cocharacters

This supporting development first proves the local adapter
`SimultaneousStandardBasisAt.hasIwahoriContractionBasis`, given a single actual
standard cocharacter for the specified root subset. It then proves
`StandardCocharacterStatement → SimultaneousBasisJacquetAdapterStatement`
and
`RelativeRootSystemStatement → SimultaneousBasisJacquetAdapterStatement`
at the original universe. Each global implication retains its algebraic input
as an explicit undischarged prerequisite. Neither proves the unconditional
adapter task. The target statement pair and its entire import closure are
unchanged.

For each actual standard parabolic the standard-cocharacter statement provides
a cocharacter. `JacquetStrictElement` lifts it integrally through the exact
compatible split component and evaluates it at the common uniformizer. This
constructs the actual strict element with all four required memberships.
Its `strictElement` definition fixes that element before the open subgroup
is introduced.
The inherited Levi basis chooses a member of the same ambient compact open
normal basis with the required literal Levi intersection. The ordered
factorization and contraction clauses of that member then supply all seven
Jacquet fields using `JacquetContractionAssembly`, including uniform opposite
contraction into every ambient open subgroup.

The proof uses the canonical `rationalPointTopology` and the same actual
standard radical, Levi and opposite radical. It retains arbitrary local
fields, both characteristics, all ranks and all allowed root subsets.
It needs only the existence clause of `StandardCocharacterStatement`; the
all-test dynamic comparison clause is not used. The root-system implication
uses the published
`exists_standardCocharacter_of_relativeRootSystemStatement` directly, without
any sign-to-dynamic comparison hypothesis. Existence of the simultaneous basis
and its geometric compact subgroup remain independent obligations.

These are internal consequences of the supplied basis clauses, the published
conditional standard-cocharacter construction, and the supporting strict-element
and contraction-assembly modules. They add no structural axiom.
