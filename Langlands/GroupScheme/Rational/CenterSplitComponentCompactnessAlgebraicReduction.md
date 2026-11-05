# Full-center point quotient compactness from three algebraic inputs

Authors: Worker 1232 and Worker 1567.

`CenterSplitComponentCompactnessAlgebraicReductionStatement.{u}` states
that `CenterMultiplicativeTypeStatement`,
`AffineNormalSubgroupQuotientStatement`, and
`MultiplicativeTypeSplitQuotientAnisotropyStatement` imply the unchanged
`CenterSplitComponentCompactnessStatement`, all in the same arbitrary
universe. `centerSplitComponentCompactnessAlgebraicReduction` proves the
implication. It applies over every nonarchimedean local field in either
characteristic. No general anisotropic reductive compactness proposition
is an antecedent.

The proof follows the published four-input
`centerSplitComponentCompactnessReduction` through construction of an
actual full-center quotient. Full-center existence supplies a closed
representative `z : Z → M`. The given split component `i : A → M`
factors through `z` on all test schemes as `j : A → Z`. Closedness and
centrality descend through the monomorphism `z`, so the full all-test
range of `j` is a normal closed subgroup. Affineness and local finite
type of `Z` follow from its closed immersion in the smooth affine `M`.
The affine quotient premise produces an actual affine locally finite
type group `C` and an fppf homomorphism `q : Z → C` whose scheme-kernel
range equals the full range of `j`. This step makes no smoothness
assumption on `Z` or `C`.

The proved split-torus quotient theorem constructs open sections on
canonical rational points. The full-center multiplicative-type premise
and the split-quotient structural premise, applied through the published
`centerQuotient` adapter, supply
`HasAnisotropicTorusFiniteQuotient C`. The proved
`HasAnisotropicTorusFiniteQuotient.isCompact_univ` now makes all of `C(F)`
compact in `rationalPointTopology F C.X`. It uses the published
anisotropic-torus compactness theorem and finite attained-image
compactness, retaining possible nonreduced finite schematic quotient
data and requiring no point-surjectivity onto that finite quotient.

Finally, the existing `centralPointQuotientModelHomeomorph` identifies
`C(F)` with the literal full scheme-center point quotient by the actual
image of `A(F)`. Its construction uses the actual factorization,
scheme-kernel equality, and the open sections. Compactness transported
through the inverse homeomorphism gives exactly the inherited center
topology and quotient topology selected in the unchanged target.
The additive uniform structure used on the field comes from its given
topological additive group and keeps its topology.

This is a derived composition of published actual-center, factorization,
local-section, structural adapter, topology, and finite-extension
torus-compactness APIs. The proof adapts the published four-input
assembly and replaces its conditional analytic step with the proved
torus-specific step. The previous assembly is preserved unchanged.
All three algebraic propositions remain explicit antecedents; this
module does not prove them or the unconditional host target.
