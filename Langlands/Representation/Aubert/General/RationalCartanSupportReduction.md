# Compact support from actual bounded Cartan expressions

This internal adapter specializes `CartanSupportReduction` to the literal
`FiniteCartanCovering` in the published Renard VI.2.1 (a) implies (c) statement.
It is a derived Library argument, not a new assertion from the literature.

`RationalCartanSupportBound` asks for one upper bound on all simple-root
pairings whenever a function has a nonzero value at
`k₁ * uniformizerPowers i (.ofAdd x) * f * k₂`, with both compact factors in
the specified subgroup, `f` in the specified finite centralizer subset, and
all simple-root pairings of `x` nonnegative. It does not assert that cuspidality
provides this bound.

`exists_cocharacter_of_mem_CAplus` extracts the actual cocharacter from the
definition of the uniformizer cone. The published norm formula, with residue
cardinality greater than one, converts its norm inequalities to nonnegative
integer pairings.

`hasCompactSupport_normKernel_of_cartanSupportBound` applies the generic
compact-support reduction to the actual rational-character valuation.
Published results put the compact subgroup in its kernel and make the kernel
closed. Each Cartan expression has an actual uniformizer parameter. Scheme
centralization permits moving its finite centralizer factor past that
uniformizer power when applying the support bound. The generic finite-fiber
argument gives compact support in the inherited topology of the actual common
norm kernel. A homeomorphism induced by the published equality of the
valuation kernel and common norm kernel transfers the compact-support result.
The finite root-label, Hausdorff, and topological-group assumptions remain explicit.

`hasCompactSupport_normKernel_of_finiteCartanCovering` selects the finite
centralizer subset from the literal covering hypothesis. Its bound hypothesis
is quantified over finite subsets, so it applies to that selected subset.
Both compactness lemmas still require joint detection of the parameters by the
simple-root coordinates and ambient rational-character valuation. The coefficient
bound and this detection input are separate from the final theorem.
