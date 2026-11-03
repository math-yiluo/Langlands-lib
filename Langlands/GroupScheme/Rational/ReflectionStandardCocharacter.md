# Standard cocharacters from actual integral reflections

This internal construction uses the published actual
`RelativeRootReflectionData i` and its crystallographic evaluation pairing
to construct standard cocharacters. It does not require that the selected
reflection representatives generate the actual relative Weyl quotient, or
that the quotient acts faithfully. It retains arbitrary universes, fields,
characteristics, possibly nonreduced relative roots, and empty root sets.

For a monomorphic torus inclusion into an affine group scheme, the imported
`RelativeRootReflectionData.neg_mem_relativeRoots` from
[`ReflectionNegation`](ReflectionNegation.md) gives negation closure of the
actual roots. Its proof applies the reflection formula to its own root:
the self-pairing is two, so its normalizing point sends that root to its
negative. The published normalizer action preserves actual relative
roots. This imported step does not need splitness, finiteness or genericity.

`RelativeRootReflectionData.linearIndependent_simpleRelativeRoots`
additionally assumes finiteness of the actual roots and genericity of the
chosen cocharacter. It constructs `D.rootPairing` from
[`RootReflectionAssembly`](RootReflectionAssembly.md), with its proved
root-system and crystallographic instances. The integral pairing with the
generic cocharacter gives a rational functional nonzero on every root.
Each actual simple relative root maps to the indecomposable positive base
of that pairing: any positive decomposition in the root span would descend
to a character decomposition by injectivity of rationalization for the
split torus, contradicting the defining indecomposability. This map is
injective because the constructed root index is the actual root subtype.
Mathlib's `RootPairing.linearIndepOn_root_baseOf` then gives independence,
and inclusion of the root span gives independence in the ambient rational
character lattice.

`RelativeRootReflectionData.exists_standardCocharacter` applies the
published split-lattice interpolation theorem
`exists_standardCocharacter_of_linearIndependent` to that independence.
The construction `standardCocharacterOfRootReflections` chooses such a
cocharacter, and its specification proves the required zero pairings on
the given subset of simple roots and strict positivity on the other
simple roots. Every subset is included, as is the empty root set.

`RelativeRootReflectionData.standardCocharacterDynamicComparison` uses
reflection negation closure and the published positive-root induction to
show that two standard cocharacters for the same subset have the same
signs on all actual roots. An explicit sign-to-dynamic comparison then
identifies their dynamic parabolic, centralizer, and unipotent subgroup
functors. This is conditional on that structural comparison.

The final two results specialize to connected reductive groups with
maximal split torus. Smoothness supplies local finite type and the
published Lie-weight finiteness theorem supplies finite actual roots.
`exists_standardCocharacter_of_relativeRootReflectionExistenceStatement`
therefore needs only the explicit intrinsic reflection-existence statement
for existence. The extra full-kernel centralization conclusion of that
statement is not needed after its reflection data have been obtained.
`standardCocharacterStatement_of_reflections_of_signs` also assumes
`RelativeRootSignsDetermineDynamicStatement` and applies the published
pointwise-intersection comparison to obtain exactly
`StandardCocharacterStatement` at universe `u`, on every test scheme.

This is a conditional prerequisite, not an unconditional proof of that
host statement. Neither intrinsic reflection existence nor sign-to-dynamic
comparison is established here. No positive-root stabilizer, parabolic
classification, Weyl generation, or Weyl faithfulness theorem is used by
this adapter. Any proof of its structural inputs must discharge its own
dependencies independently.

The provenance is internal: the actual reflection-pairing construction is
due to the published root-system development, the rational base argument
adapts the earlier `RelativeRootStandardCocharacter` proof to that pairing
directly, the lattice interpolation is the published
`IndependentStandardCocharacter` construction, and the sign and
intersection arguments reuse `PositiveRootInduction` and
`StandardCocharacterReduction`. No new external geometric assertion is
claimed.
