# Fourier identities for packed ordered Schwartz tensors

This module contains the seven identical helpers formerly private to
`ConstantCoefficientEllipticL2EstimateProof` and
`OrderedTensorL2InterpolationProof`. Both proof modules now import this shared
implementation under `Langlands.Analysis.OrderedTensorFourier`. The extraction
preserves their definitions, hypotheses and proof bodies; it changes only
visibility and namespace. Both public estimate statements and theorems retain
their meaning.

Worker 94 authored these arguments. They were published with Worker 383's
constant-coefficient estimate contribution and independently accepted with
Worker 1144's interpolation contribution. The Integrator consolidated the
identical copies. These are internal derived arguments built on Mathlib,
with its canonical volume and Fourier normalization.

- `packSchwartz g` packs a finite family `g : W → 𝓢(V, ℂ)` into one
  Schwartz function with values in the actual Euclidean space
  `EuclideanSpace ℂ W`. It is the finite sum over `w` of the
  postcompositions of `g w` with `z ↦ z • single w 1`.
  `packSchwartz_apply` recovers coordinate `w` at `x` as `g w x`.
- `fourier_postcomp` commutes the Fourier transform with
  postcomposition by a continuous linear map, using
  `ContinuousLinearMap.integral_comp_comm` on the Fourier integral.
  `fourier_packSchwartz` then gives `𝓕 (packSchwartz g) =
  packSchwartz (𝓕 ∘ g)` by `FourierTransform.fourier_sum`.
- `eLpNorm_fourier_schwartz` is Plancherel in extended form:
  `eLpNorm (𝓕 f) 2 volume = eLpNorm f 2 volume` for a Schwartz `f`.
  It comes from `SchwartzMap.norm_fourier_toL2_eq`. Both extended norms
  are finite, so `ENNReal.toReal` is injective on them.
- `fourier_orderedDeriv` proves that the iterated line derivative of a
  scalar Schwartz `f` along `e (w 0), …, e (w (r-1))` has Fourier
  transform `(2πi)^r (∏ j, ξ (w j)) 𝓕f(ξ)`. The proof is induction on
  the word length. The empty word is the base case. The successor step
  uses `iteratedLineDerivOp_succ_left`,
  `SchwartzMap.fourier_lineDerivOp_eq`, the coordinate formula
  `EuclideanSpace.inner_basisFun_real` and `Fin.prod_univ_succ`.
- `orderedFrequencyTensor_norm` proves the ordered frequency tensor
  identity. The vector `(∏ j, ξ (w j))_w` in
  `EuclideanSpace ℂ (Fin r → Fin d)` has norm `‖ξ‖^r`. After squaring,
  `Fintype.sum_pow` expands `(∑ i, ξ i ²)^r` into the sum of squared
  products over all ordered words, repeated letters included.

The finite sums and products include empty coordinate sets and empty words.
The helpers cover zero dimension and order zero without additional hypotheses.
They add no elliptic estimate, interpolation inequality or analytic regularity
claim; those conclusions belong to their respective proof modules.
