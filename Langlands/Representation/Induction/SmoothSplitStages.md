# Smooth induction in stages along a split projection

Let `Q ≤ P` be subgroups of a topological group `G`. Let `p` be a
continuous homomorphism from `P` to a topological group `L` with
a continuous homomorphic section `s`. Suppose `Q` is the inverse
image in `P` of a subgroup `H` of `L`. Pull a complex representation
of `H` back to `Q` by the restriction of `p`.

`smoothSplitStagesEquiv` identifies its smooth induction to `G` with
the smooth induction from `P` of the `p`-inflation of the smooth
induction from `H` to `L`. The ordinary induction-in-stages
equivalence first makes the inner functions live on `P`. Their
coefficients are trivial on the kernel of `p`, so the split-quotient
equivalence replaces them by functions on `L`. Relabeling the inner
subgroup by equality preserves evaluation.

The forward map evaluates a direct section at `s(l) * g`. Its inverse
evaluates the inner section at the identity. In particular, the inverse
evaluation formula can be used to compare the induced twisting
operators by their values as functions.

The construction combines the two function-space equivalences
`smoothStagesEquiv` and `smoothSplitQuotientEquiv`. Its mathematical
source is the smooth induction in stages of Bernstein–Zelevinsky
(1977), §§1.8(a) and 1.9(c), pp. 444–445, here in the unnormalized
split-projection setting.
