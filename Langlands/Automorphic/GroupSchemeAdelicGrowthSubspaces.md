# Embedding independence of the existing full adelic growth spaces

Fix a number field `F` in any universe, an actual affine group scheme `G`
over `Spec F`, and two matrix representations `rho` and `sigma` with
positive ranks. Assume both representations are scheme-theoretic closed
immersions, using the existing `GroupScheme.IsClosedSubgroup` predicate.

`adelicGrowthSubrepresentation_eq_of_closedImmersions` proves equality
of the existing full adelic growth subrepresentations inside
`ContinuousRationalFunctions F G`. Their membership conditions are the
natural-exponent bounds for the existing dimension-scaled full adelic
heights. The proof applies the polynomial-growth part of the published
`closedImmersionAdelicGrowthIndependence` theorem to each original
continuous rational-invariant function. The existing real-exponent
moderate-growth conditions define these same subspaces.

Intersecting with the unchanged finite plot-smooth subrepresentation
proves equality of `finitePlotSmoothAdelicGrowthSubrepresentation`.
This retains smooth infinite slices and a common open finite stabilizer.
The two `ChangeRepresentation` linear equivalences are restrictions of
the identity to the equal submodules. Their forward and inverse value
lemmas identify the original continuous function. They intertwine the
existing full adelic right action with convention `R(g)f(x) = f(x*g)`.

For a fixed relative dimension, smooth structure `hsmooth` and scalar
commutator premise `hcalc`, the uniform part of the same published theorem
proves equality of `adelicUniformGrowthSubmodule`. The finite right-action
subrepresentations therefore agree too. The original uniform predicates
choose one exponent before every actual enveloping element; this
quantifier order is supplied by the imported theorem. The uniform
`ChangeRepresentation` linear equivalence and its inverse keep the
original finite plot-smooth function. Its compatibility lemmas
intertwine both positive finite right translation and the existing
`adelicUniformGrowthEnvelopingAction` for the same enveloping element.

This is an internal consumer construction. All mathematical input is the
published full adelic growth-independence proof and the definitions of
the existing subspaces and actions; there is no additional external
source assertion. The comparisons require the explicit positive-rank
closed embeddings. They construct no embedding, change no function
carrier, and identify no chosen smooth atlases. In particular the finite
plot-smooth carrier is not identified with the algebraic tensor product
in Getz--Hahn (6.1). Automorphic finiteness, cuspidality, quotient measures,
reduction theory and square integrability retain their existing separate
conditions.
