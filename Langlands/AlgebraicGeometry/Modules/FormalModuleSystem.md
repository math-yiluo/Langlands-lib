# Actual module systems on adic thickenings

`Modules.FormalModuleSystem f I` consists of actual module sheaves on
`X_n = X ×[Spec R] Spec(R / I^(n+1))`, with a specified isomorphism from
the ordinary pullback of the next sheaf to the current sheaf. It reuses
the actual quotient spectra, fibre products and transition arrows in
`Picard.FormalLineBundleSystem`. The definition imposes no finiteness,
properness or completeness condition.

This is the module-system formulation of the Stacks Project, Section
30.27, Remark 30.27.2, retained in the registered source
`stacks-formal-line-bundle-effectivity-2026-11-03` at
`literature/Stacks Project - Grothendieck existence and compatible formal
module systems (2026-11-03)/0CYW.html`. Here the index is shifted from the
source's `n ≥ 1` to natural numbers with exponent `n+1`. The source requires
coherent terms for its existence theorem. This interface allows arbitrary
terms so that finiteness can be stated separately.

`ofModule` is the ordinary restriction system of an actual module sheaf.
Its transition is the module pullback composition isomorphism followed by
the comparison for the projection triangle. `Comparison` stores actual
component isomorphisms and a commutative square for each transition.
Identity and composition satisfy these equations by functoriality and
the given squares. `IsAlgebraization` requires a single comparison of
the whole system, rather than unrelated component isomorphisms.

For an actual line-bundle system, `toModuleSystem` forgets local rank one
through the published full subcategory. The canonical restriction system
then has a comparison with `ofModule`, whose component maps are the identities.
The proof checks the pullback-composition square for arbitrary scheme
morphisms first, and then applies it to the adic projections and transitions. A compatible comparison can be forgotten,
and any compatible module comparison between such line-bundle systems
lifts back through the full subcategory. The lifting proof uses the
same component isomorphisms and the underlying commutative squares;
faithfulness verifies their equality in the full subcategory.

Consequently `isAlgebraization_of_module` proves that a module
algebraization which is already locally free of rank one gives an actual
line-bundle algebraization with the same transition compatibility.
These comparison constructions and elementary proofs are derived
interface results. No coherent existence, rank-one lifting, or proper
formal effectivity theorem is asserted here. In particular local rank
one in the last lemma is an explicit premise.
