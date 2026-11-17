# Reduction of split root lines to proportional-root centralizers

`Langlands.GroupScheme.splitRootLieLine_of_rankOne` is an internal conditional
reduction at arbitrary universe `u`. Its conclusion is the exact proposition
`SplitRootLieLineStatement.{u}`. It retains two explicit inputs:
connected reductivity of actual cocharacter centralizers
(`DynamicCentralizerReductiveStatement.{u}`), and the root-line assertion for
connected reductive groups with a split maximal torus whose roots are pairwise
linearly dependent over the integers. This theorem does not discharge either
input and is not an unconditional proof of the conclusion.

Fix a root `χ` of the given split maximal torus over the arbitrary field `k`.
The finite ambient root set allows the construction of a cocharacter `ζ` that
pairs to zero with `χ`, with every root pairing to zero with `ζ` dependent on
`χ`. The proof uses the existing lattice construction
`RootReducedness.kernelCocharacter` and its two properties.

Let `L` be the actual affine centralizer scheme of `ζ` in `G`. The first input
makes `L` connected reductive. The torus factors through `L`, and maximality
passes to this factor because the centralizer inclusion is closed.
`RootReducedness.mem_roots_torusFactor` keeps `χ` as a root in `L`, while
`RootReducedness.mem_roots_of_mem_roots_torusFactor` shows that every root of
`L` is an ambient root annihilating `ζ`. The lattice properties then show that
the roots in `L` are pairwise dependent. Applying the second input gives the
line trivialization in `L`.

Finally `Dynamic.nonempty_line_torusFactor_iff` transports that trivialization
through the actual centralizer differential to the ambient `χ`-weight space.
That equivalence is constructed in
`Dynamic/CentralizerWeightSpace`. The argument never extends the field, and
adds no perfectness, characteristic or algebraic-closedness assumption.

The provenance is the generic centralizer reduction already implemented for
root reducedness and full root tangents in
`Reductive/RootReducednessReduction` and
`Reductive/RootTangentRankOneReduction`, now applied to actual character
weight spaces. The finite-lattice and differential lemmas used here do not
assert root reducedness or the root-line property.

## Dependency audit

The private breadth-first type-and-value closure audit described in
`Dynamic/CentralizerWeightSpace.md` was also run from
`Langlands.GroupScheme.splitRootLieLine_of_rankOne`. At Library base
`ab9053b1751d6b6557d044c38c04e4c8a67dfffc`, check
`46c38be4-566c-4dcb-895c-ce735568d2ce` reached 44,862 constants, including
1,047 `Langlands` constants. It reported no missing constants and no occurrence
of any of the 24 excluded statement, proof or helper names listed there.
The theorem's only axioms are `propext`, `Classical.choice` and `Quot.sound`.
Both modules compiled with zero errors and zero warnings in check
`0add441b-f5a9-4bc3-8874-71a61a72e225`.

The proof uses finite-lattice linear algebra, actual centralizer
representability, weight-space transport and the two explicit inputs. It
constructs no Borel subgroup, regular cocharacter, root datum or root cell.
Independence of a future unconditional application also requires independence
of the proofs supplied for its two inputs.
