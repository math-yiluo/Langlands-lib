# Conditional quasicuspidal Jacquet spectrum comparison

Author: Worker 320.

This module proves
`Langlands.Aubert.QuasicuspidalJacquetSpectrumStatement.{uF,uV} F T`
as `Langlands.Aubert.quasicuspidalJacquetSpectrum`. It preserves the
statement's arbitrary prime, supplied p-adic field and compatible topology,
independent field and carrier universes, saturated carriers, actual exact
Grothendieck classes, and normalized upper Jacquet convention.

Assume actual admissible finite-length representations `π, τ`, a sign
`ε ∈ {1,-1}`, and `D[π] = ε[τ]`. Assume that the actual reversed Jacquet
module of `π` is nonzero and quasicuspidal. The conclusion determines `ε`
and equates generalized block-scalar character occurrence for `J_B(τ)` and
the literal reversal transport of `J_(B.reverse)(π)`.

## Implemented proof

Write `JR = J_(B.reverse)(π)`, `JT = J_B(τ)`, and let `C` be the actual
whole-Levi reversal transport of `JR` to the Levi of `B`.

First, `normalizedJacquetK0_hasFiniteLength` supplies finite length of
`JR` and `JT`. `transportFunctor_preservesFiniteLength` supplies finite
length of `C`. The published `quasicuspidalJacquetClass` determines
`ε = (-1)^(n - B.length)` and equates the virtual Jacquet classes.
Rewriting with `normalizedJacquetK0_finiteLengthClass` and
`leviTransportK0_finiteLengthClass` identifies this equality with the
canonical actual exact classes of `JT` and `C`.

Second, `Parabolic.isAdmissible_normalizedJacquet` supplies admissibility
of both actual Jacquet modules from admissibility of `τ` and `π`.
`CuspidalSupport.isAdmissible_transport` then supplies admissibility of
`C`. This transport is pullback by the actual inverse continuous Levi
conjugation; it retains the Jacquet carrier.

Third, the proof prepares the hypotheses of
`Langlands.exactClassCentralSpectrum` for the actual target product Levi.
For each open Levi subgroup, `T.leviCompactOpen` supplies a compact open
subgroup contained in it. The block-scalar homomorphism is restricted to
the full Levi center using the published
`blockScalarLevi_mem_center`. Its continuity follows componentwise from
`GeneralLinear.scalarContinuous`; taking values in the center uses the
subtype topology.

The exact-class spectrum theorem now applies to `JT` and `C` with this
continuous central map. Both restricted actions are definitionally the
actions in the target statement. In particular, the second is the literal
inverse-conjugation transport followed by the target block-scalar map.
The proof makes no coordinate-reversal identification.

## Scope and provenance

This is an internal assembly of published algebraic and admissibility
results, rather than a transcription of a new original-source theorem.
Its mathematical inputs are the conditional quasicuspidal Jacquet-class
comparison, exact-class central-spectrum invariance, actual normalized
Jacquet admissibility, continuous whole-Levi transport, and the compact
open basis of the actual p-adic Levi.

The equivalence concerns arbitrary algebraic characters and generalized
occurrence with one common power per vector. It preserves the character
without specifying a common vector or a common power across the two
objects. A character with open kernel yields the corresponding exponent
comparison by adjoining that same condition to both sides.

The theorem is conditional on a supplied signed Aubert image and on
nonzero quasicuspidal reversed Jacquet data. It does not construct an
image, deduce representation equivalence from exact-class equality, or
establish an analytic square-integrability criterion. It supplies no
single-segment classification. No multisegment exhaustion, ordered
strong-head coverage, or downstream Langlands classification is used.
