# Actual operators on all automorphic forms

This internal construction uses the published compact-translation,
differential compact-finiteness and differential-growth proofs to identify the
actual maximal operator core with the entire automorphic form space. It works
over any number field `F : Type uF`, in every natural rank `n`, with complex
coefficients and the existing standard infinite compact subgroup. It introduces
no preservation or nonzero-form assumption.

`automorphicDifferentialPreservation` applies the published equivalence in
`PreservationStatement` to the two differential preservation proofs.
`automorphicOperatorCore_eq` then applies the equivalence in `CompactAction`,
which already incorporates the proved compact-translation closure. Consequently
the two submodules of the same finite-smooth rational-invariant function space
are equal. This discharges the remaining closure condition of that existing
core construction without changing its definition.

`stableAutomorphicEquiv` is Mathlib's continuous complex-linear equivalence
between these equal submodules. Both spaces carry their existing subspace
topologies, ultimately induced from compact-open continuous adelic functions.
Its forward map is the existing `stableAutomorphicInclusion`; its inverse
retains exactly the underlying finite-smooth function. The continuity assertion
concerns this identification of equal spaces.

`fullAutomorphicSubrepresentation` uses the original automorphic submodule and
the proved core equality to establish invariance under every element of the
concrete operator algebra. `fullAutomorphicAction` is restriction of those
actual ambient operators to all forms. `fullAutomorphicAlgebraAction` retains
addition, multiplication and complex scalars, proved by the faithful subtype
map. Composing it with the existing `differentialOperator` constructs
`automorphicEnvelopingAction`, a complex algebra homomorphism acting by the
genuine enveloping differential on every form.

The three `fullAutomorphicAction_...Operator` formulas identify its restrictions
with the existing finite adelic translation, the existing standard compact
translation and the new full-form enveloping action. The `..._val` formulas
identify their underlying finite-smooth functions. The faithful
`fullAutomorphicFiniteSmoothInclusion` intertwines the whole concrete operator
algebra. `stableAutomorphicOperatorEquiv` equips the same underlying linear
identification with its operator intertwining proof; the four
`stableAutomorphicEquiv_...Action` formulas also expose the whole-algebra,
finite, compact and differential identities for the continuous identification.
Finally `automorphicFiniteRightAction_envelopingAction` proves commutation on
all forms by the existing ambient commutation identity and subtype injectivity.

This constructs algebraic actions of the same actual operator algebra. It does
not assert continuity of differential operators for the compact-open subspace
topology, a full infinite-group action preserving compact-finite forms, spectral
existence, irreducibility, tensor factorization or automorphic classification.
Those remain distinct questions. The internal provenance consists entirely of
the named published preservation proofs, the existing concrete core and action
constructions, and Mathlib's equivalence of equal submodules; no new
original-literature identification is claimed.
