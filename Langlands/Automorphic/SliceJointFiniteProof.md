# Joint differential finiteness of actual automorphic slices

Author: Worker 94. Module: `Langlands.Automorphic.SliceJointFiniteProof`.
The theorem `Langlands.Automorphic.automorphicSliceJointFinite` proves the
unchanged `AutomorphicSliceJointFiniteStatement K n` for arbitrary
`K : Type u` with `[Field K] [NumberField K]` and every natural rank `n`,
including zero.

Given an actual `f : SmoothRationalFunctions K n` satisfying
`IsAutomorphicForm K n f`, and any finite adelic argument `b`, the conclusion is
`ArchimedeanGL.IsJointFinite K n (smoothInfiniteSlice K n b f)`.
This is finite complex dimension of the actual joint orbit span under the
genuine center and compact enveloping actions on that same smooth slice.

## Implemented proof

The proof composes three published results.

1. The first part of `SliceFinitenessProof.sliceFiniteness` evaluates the
   simultaneous center-finite family `smoothSliceFamily K n f` at `b`.
   The hypothesis is exactly the center component of `IsAutomorphicForm`.
   The resulting function is definitionally `smoothInfiniteSlice K n b f`,
   and its actual center orbit is finite.
2. The second part of `SliceFinitenessProof.sliceFiniteness`, applied to
   `standardInfiniteCompact K n`, transports the compact component of
   `IsAutomorphicForm` to finite orbit of that slice under the actual smooth
   right translations of this subgroup.
   `ArchimedeanGL.compactGroupFiniteDifferential` converts that group orbit
   finiteness to `IsCompactLieFinite` for the same slice.
3. `ArchimedeanGL.separateJointFinite` combines these center and compact
   differential finiteness statements to give the claimed `IsJointFinite`.

The automorphic hypothesis is retained in full. In particular, the proof starts
from the single simultaneous center condition on the whole family, which is
equivalent to one common finite-codimensional center ideal. Evaluation is used
only to obtain its consequence for the selected slice. Finite level and
polynomial growth remain in the premise, though this composition uses only the
compact and center components.

The final Lean example exposes the entire universe and parameter telescope.
No positive-rank assumption or ambient finite-dimensionality is introduced.
The conclusion is separate for each `b`; no uniform dimension bound is claimed.

## Provenance and scope

This is an internal derived composition of the published slice transport,
compact-group differential bridge, and separate-to-joint finiteness theorems.
Their implementations are imported by Lean name; this file does not reproduce
or modify their proofs. No new theorem from the literature is invoked.
The unchanged statement's Markdown records the intended composition and scope.

Joint differential finiteness supplies a prerequisite for reproduction. This
file proves no reproducing kernel, convolution approximation, analytic
regularity, or polynomial growth of enveloping derivatives.
