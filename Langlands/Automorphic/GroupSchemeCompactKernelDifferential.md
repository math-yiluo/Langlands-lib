# Enveloping operators and weighted compact integration

`Langlands.Automorphic.GroupSchemeFunctions.CompactKernelEnvelopingActionStatement` concerns the
actual complex enveloping action on plot-smooth functions on `G(F_∞)`. Let `F` be a number
field and `G` an affine group scheme over `F` with a chosen smooth relative dimension `d`.
Use the atlas `smoothChartedSpace F G hsmooth` and the action
`plotSmoothEnvelopingAction F G hsmooth hcalc` for the supplied
`AdelicDifferentialCommutator` witness `hcalc`.

Let `k(x,y)` be a jointly smooth complex-valued kernel on the product of `G(F_∞)` and a
smooth real manifold modeled on a normed real vector space. Choose a compact topological
space `C` with its Borel σ-algebra, a finite measure `μ` on it, a continuous complex weight
`a` and a continuous map `j` from `C` to the second manifold. For each enveloping operator `D`,
the theorem produces a jointly smooth kernel `k_D`. It equals `D` applied to the first variable
at each fixed second variable. With the plot-smooth structure on the average,
applying `D` to `∫ a(z) k(·,j(z)) dμ(z)` gives `∫ a(z) k_D(·,j(z)) dμ(z)`.

## Implemented proof

For an identity tangent vector `X`, apply the tangent map to the smooth kernel
`((x,y),t) ↦ k(xt,y)`. Evaluate at the zero tangent over `(x,y)` and the tangent `X` over the
identity `t = 1`. The result is the first-variable orbit derivative and is jointly smooth.
The derivative part of `compactManifoldVectorIntegral` then gives the integral identity at
`t = 1`, with `x` fixed.

For sums and complex scalar multiples, the proof uses linearity of the action and the
integrability of the compact weighted kernels. For a product of operators, apply the two
operators successively to the kernel and to the integral. Equality of smooth functions follows
from their pointwise values, so these identities apply to all proofs of plot-smoothness. The
actual action on complexified tangent generators is the scalar extension of the real orbit
derivative. Induction in the tensor algebra, using its surjection onto the enveloping algebra,
then gives the result for every `D`.

## Provenance

This is an internal consequence of `compactManifoldVectorIntegral`, the comparison
`isPlotSmooth_iff_contMDiff` and the actual action `plotSmoothEnvelopingAction`. The theorem
`adelicDifferentialCommutator_of_smooth` supplies the commutator witness for this atlas. The
interchange with the Levi differential action transfers a common center annihilator through
the integrated induced action.
