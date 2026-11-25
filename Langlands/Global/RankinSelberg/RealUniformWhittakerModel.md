# A real coefficient space with uniform growth under differentiation

This internal refinement introduces a new coefficient space
`realUniformWhittakerModel r ds a`. It preserves every declaration and statement about
the earlier `realWhittakerModel`. The refinement rests on
the distinction between a separate polynomial exponent for each derivative and one
exponent valid for every derivative word.

`IsRealUniformWhittakerIntertwiner r ds a B` requires the five existing conditions of
`IsRealWhittakerIntertwiner`: left upper-unipotent covariance for the fixed character
`realWhittakerCharacter a`, smoothness, polynomial growth, compact equivariance, and
compatibility with the genuine real standard-module Lie action. It additionally
requires a natural exponent `N` chosen before every source vector `f`, with
`‖B f g‖ ≤ C * realMatrixHeight(g)^N` for a nonnegative constant `C` depending on `f`.

The new space is the algebraic supremum of the ranges of all such maps. Thus its
members are finite linear combinations of their coefficients. It is a subspace of
the earlier model (`RealUniformWhittaker.model_le_model`). Its definition asserts no
equality with the Whittaker space of a continuous globalization.

The module proves `RealUniformWhittakerRegularityStatement`: each member has smooth,
left-character-equivariant derivative words, and one polynomial exponent works for
all finite words of real matrix right derivatives. Constants may depend on the word
and the function; the exponent may depend on the function. The derivative words use
the existing right fold, so the first direction acts after the directions in the tail.

The proof has two parts. The first assertion follows from inclusion into the earlier
model and its proved derivative regularity. For the common exponent, smooth functions
with `∃ N, ∀ word, ∃ C ≥ 0` bounds form a submodule `uniformGrowthFunctions`. List
induction proves smoothness, additivity and complex homogeneity of derivative words
from the corresponding one-derivative results. The zero function has exponent zero.
For sums, the larger exponent works for every word because `realMatrixHeight ≥ 2`;
the word-dependent constants add. Scalar multiplication preserves the exponent and
multiplies the constants by the scalar norm.

For a generating coefficient `B f`, list induction and the specified intertwining
condition express each derivative word as `B f'`, where `f'` is a vector obtained by
the genuine Lie action in the same standard module. The common source-vector exponent
therefore bounds every word. Supremum containment in `uniformGrowthFunctions` extends
this to the full algebraic coefficient space.

Provenance is internal: all constructions are explicit refinements and elementary
consequences of the earlier coefficient definition, the Library's standard-module Lie
action, and the proved height lower bound. This result establishes neither convergence,
continuation nor a functional equation. It does not assert that the refined and earlier
models coincide, or that every earlier-model function has uniform derivative growth.
