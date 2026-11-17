# Analytic multiplier families on finite compact layers

This internal construction derives analytic dependence from the published
Fourier formula for `blockFrobMap`, finite Fourier support, and the finite
compact degree layers of `RealKTypeCount`. It introduces no topology on the
whole space of compact-finite standard-module functions.

`IsWeaklyAnalyticAt f z₀` means that every algebraic complex linear functional
applied to the vector family `f` is analytic at `z₀`. Constant families have
this property, and applying a fixed linear map preserves it.

`fourierEval` packages a block Fourier coefficient at a fixed group point as a
linear functional. `exists_uniform_bound` proves that a finite-dimensional
subspace has a single bound on its Fourier modes, valid for all its vectors
and all compact points. The proof bounds the modes of a finite basis and uses
linearity to extend the bound to their span.

Every supplied block Frobenius map commutes with compact translation, without
a recurrence hypothesis, and consequently preserves the compact degree layers.
Suppose a family of input vectors lies in one fixed degree layer and is weakly
analytic at `z₀`. Suppose also that each coordinate of a multiplier family is
analytic there and that its members supply block Frobenius data with fixed
source, target, position, parity and symmetry sign. Then
`analyticAt_compact_eval` proves analytic dependence of the output at every
compact point. The common Fourier cutoff turns the output formula into a
finite sum of products of analytic scalar functions.

`weaklyAnalyticAt_blockFrobMap` proves the stronger conclusion that every
algebraic linear functional on the target has analytic output. The outputs
lie in one finite target degree layer. On that layer, each functional is a
finite linear combination of compact point evaluations, by the published
separating-family lemma. The compact evaluation result therefore suffices.

These conclusions concern supplied families at fixed endpoint exponents.
They do not assert removal of an operator pole or Lie intertwining of a
limiting value.
