# Proof of the scalar constant-coefficient elliptic Fourier estimate

`Langlands.Analysis.constantCoefficientEllipticL2Estimate` proves the
published `ConstantCoefficientEllipticL2EstimateStatement d r` for every
dimension and order. It imports the unchanged statement and uses the
actual Euclidean space, standard basis, canonical volume and extended
L² norms. Worker 94 authored this proof; Worker 383 recompiled it
against the published imports and submitted it.

The Fourier helpers are shared with the interpolation proof through
[`OrderedTensorFourier`](OrderedTensorFourier.md), in the namespace
`Langlands.Analysis.OrderedTensorFourier`. Their definitions and proof bodies
are unchanged by that extraction.

The proof packages finitely many scalar Schwartz functions as a
function with values in the actual Euclidean tensor space. The helper
`orderedFrequencyTensor_norm` expands the sum over every ordered word by
`Fintype.sum_pow` to identify the frequency tensor norm with `‖ξ‖^r`.
It includes empty words and empty coordinate sets. `packSchwartz` uses
actual Euclidean coordinate vectors, and its evaluation theorem recovers
each original scalar function. Fourier postcomposition uses continuous
linear maps under the Bochner integral; finite packing then commutes
with Fourier transformation.

`eLpNorm_fourier_schwartz` transfers Mathlib's Schwartz Plancherel theorem
to the extended L² norm. The Schwartz norms are finite, which justifies
injectivity of `ENNReal.toReal` in this step. This does not identify
infinite norms through their real projections.

`fourier_orderedDeriv` proves the exact multiplier
`(2πi)^r ∏ j, ξ (w j)` by induction on the word length. The base case is
the empty derivative word. The successor case uses Mathlib's
`fourier_lineDerivOp_eq`, evaluation against the standard orthonormal
basis, the tail word and the finite-product successor formula.

`schwartzConstantCoefficientEstimate` proves the L² bound with constant
`c⁻¹` for an actual Schwartz function. Its packed derivative tensor and
scalar action are both Schwartz functions. Their Fourier transforms
equal the common factor `(2πi)^r 𝓕f(ξ)` times the frequency tensor and
scalar symbol respectively. The tensor-norm identity and assumed symbol
lower bound give the pointwise norm inequality without division by the
common Fourier factor. `eLpNorm_le_mul_eLpNorm_of_ae_le_mul` lifts the
inequality to L², and Plancherel transfers it to the original functions.
The proof includes every dimension and order, including zero.

These helpers are internal derived arguments using Mathlib, not separate
literature theorem transcriptions. The target is a derived scalar,
globally compactly supported formulation related to Morrey–Nirenberg
1957, section 5, Lemma 5.1, with the exact inverse lower-bound constant
and Mathlib's 2π normalization. The published statement Markdown records
the registered original, the comparison with the source's local system
estimate and the Fourier normalization. This proof uses the direct
global Schwartz argument rather than enclosing support in a ball.

The final theorem turns the given smooth compactly supported function
into a Schwartz function with `HasCompactSupport.toSchwartzMap`. This
preserves its pointwise values definitionally. The iterated line
operator equals `iteratedFDeriv` evaluated on the ordered standard basis
word by `SchwartzMap.iteratedLineDerivOp_eq_iteratedFDeriv`.
`packSchwartz_apply` and `EuclideanSpace.norm_eq` identify the packed
norm with the exact real square-root sum in the statement. Evaluating
the finite scalar Schwartz sum gives the exact principal action.
Finally `eLpNorm_norm` identifies the real norm function's extended L²
norm with the vector-valued one and transfers the Schwartz estimate.
No extra Fourier, integrability or derivative identity is assumed.

All helper arguments cover order zero, zero dimension and their
intersection. Empty finite products, sums and Euclidean tensor spaces
retain their actual Mathlib meanings; no positive-order or
dimension hypothesis is introduced. The result proves the displayed
constant-coefficient estimate. Variable coefficients, cutoffs,
factorial bounds, elliptic analyticity and automorphic growth remain
separate obligations.
