# Exact filtered colimits of original nondegenerate modules

This file proves the complete unchanged
`NondegenerateModuleFilteredColimitsStatements.FilteredColimitAssertions`,
with independent coefficient, index and residual carrier universes.
It imports the published statement and dependency pairs by their Lean names.

The proof constructs filtered colimits from the published actual
finite-support sum cofans and the published abelian coequalizer
construction. Exactness of filtered colimits in abelian groups descends
to the index universe; the forgetful functor from integer-unitized
modules preserves colimits and preserves and reflects finite limits.
The canonical integer-unitization equivalence then gives exact
filtered colimits of original additive nonunital modules.

The original nondegenerate inclusion is full and faithful, exact by the
published kernel and cokernel results, and a left adjoint to the actual
nondegenerate-part functor. It therefore preserves colimits and preserves
and reflects finite limits. The standard transfer lemma for exact
colimits gives Mathlib AB5 for the actual nondegenerate category.

For the concrete conclusion, evaluation detects short exactness of a
diagram short complex: monomorphisms and epimorphisms are pointwise,
and its homology object is zero when all evaluations have zero homology.
The exact colimit functor then preserves that short exact sequence.

The helper `filteredColimits` proves actual sized colimit existence.
`exactFilteredColimits` supplies the data-bearing Mathlib AB5 structure,
while `mathlibAB5` wraps it in the proposition's `Nonempty` certificate.
`shortExactColimits` proves the concrete diagram assertion, and
`filteredColimitAssertions` conjoins these unchanged closed targets.
The six distinct universe permutations check that no coefficient,
index or residual carrier levels have been identified. The carrier is
always `max uI uM`; the proof imposes no coefficient-size bound.

This implements the ambient-module route suggested in Renard I.6,
French edition dated 9 July 2026, printed pp.27–28 / PDF pp.33–34,
registered as `renard-2026-representations-groupes-reductifs-padiques`,
SHA256 `7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`.
The source's complex-algebra case is retained by the disclosed
arbitrary-ring extension. No proof of a generic comparison between
source AB5 and Mathlib AB5 is claimed.
