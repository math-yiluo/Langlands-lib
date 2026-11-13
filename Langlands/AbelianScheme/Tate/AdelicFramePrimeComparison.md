# Actual prime extraction in local adelic-frame coordinates

This internal unit derives a local factorization from the actual tensor-algebra
Tate frame and the normalized finite-adelic scalar comparison. Its inputs are an
abelian scheme over an arbitrary scheme universe, a rational algebra action, a
rational module with compatible algebra action, a field-valued point, and a chosen
actual adelic frame on the scalar extension of that module.

`adelicFrameRatLinear` forgets tensor-algebra linearity while preserving the
existing rational module structures. The proof identifies rational scalars in
both tensor-algebra representations through their algebra homomorphisms and
installs the resulting scalar towers. `adelicFrame_tmul` then applies frame
linearity to `(1 tensor a)` acting on `(1 tensor x)`. The two actual tensor-action
formulas identify its image with the finite-adele action by `a` on the frame
image of `(1 tensor x)`.

For a finite place `v` of the rationals, `localFrameToPrime` is a rational linear
map from the completion at `v` tensor the original rational module to the actual
rational prime-adic Tate module at the prime selected by `primesEquiv v`. On a
pure tensor `c tensor x`, it applies the completion-to-p-adic algebra equivalence
to `c` and lets that scalar act on actual prime extraction of the frame image of
`1 tensor x`. The tensor universal property constructs the map from this
rational bilinear formula. No extra choice of a completion-module structure on
the Tate space is needed.

`localFrameToPrime_evaluation` states that evaluating the finite-adelic
coefficients of any source vector and applying this map gives actual prime
extraction of its frame image. Tensor induction reduces the proof to pure
tensors, where `adelicFrame_tmul` and the actual finite-adelic prime-scalar
compatibility establish the identity. The additive step uses linearity.
`localFrameToPrime_inverseFrame` substitutes the inverse frame image of an actual
full rational Tate section and cancels the frame equivalence. It therefore
recovers the actual selected prime coordinate from evaluated inverse-frame
coordinates.

These are internal consequences of the imported frame and scalar-action
constructions. They assert a rational linear factorization, without an
injectivity or surjectivity claim for its local map. The specialization to Harris
frame coordinates, naturality for rational self-isogenies, one-prime
faithfulness, finite order, and the exact CM small-level rigidity theorem remain
separate obligations.
