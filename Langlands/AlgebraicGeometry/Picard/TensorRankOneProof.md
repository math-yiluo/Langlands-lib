# Local rank one of tensor powers of line bundles

The theorem
`Langlands.AlgebraicGeometry.Picard.tensorPow_isLocallyFreeRankOne`
has exactly the published type
`Langlands.AlgebraicGeometry.Picard.TensorPowLocallyFreeRankOneStatement.{u}`.
Thus, for every scheme `X : AlgebraicGeometry.Scheme.{u}`, every
`L : LineBundle X` and every `n : ℕ`, the actual module sheaf
`Langlands.Scheme.Modules.tensorPow L.obj n` is locally free of rank one.
The universe `u` is arbitrary, and the theorem has no extra hypotheses.

## Implemented proof

The proof introduces `X`, `L` and `n` and inducts on `n`, following the
published recursion for the actual sheaf tensor powers.

At zero, `tensorPow L.obj 0` is definitionally `structureSheaf X`, namely
`SheafOfModules.unit X.ringCatSheaf`. The local rank-one property of
`LineBundle.trivial X` proves this case.

At a successor, the goal is local rank one of
`tensorObj L.obj (tensorPow L.obj n)`.
The published lemma `IsLocallyFreeRankOne.tensor` applies to `L.property`
and the induction hypothesis. Its comparison premise is supplied by the
unconditional published theorem
`Langlands.Scheme.Modules.pullbackTensorComparisonIsIso`, imported from
`Langlands.AlgebraicGeometry.Modules.PullbackTensorProof`.
Consequently the proof retains no pullback tensor comparison premise.
The binary closure lemma uses intersections of trivializing opens,
pullback compatibility of the actual sheaf tensor, and its explicit unit
isomorphism, as described in `LineBundleTensor.md`.

## Provenance and scope

This is an internal derived induction by Worker 5 on the published tensor
construction, using published local tensor closure and the published
comparison proof by their Lean names. The target statement and its
imported constructions are unchanged.

The original mathematical context is Stacks Project Definition 17.14.1
(tag 01C6), Lemmas 17.25.4 (tag 0B8M) and 17.25.5 (tag 01CT), and
Definition 17.25.6 (tag 01CU), in the registered source
`stacks-local-freeness-invertibility-sections-2026-10-21`, content SHA-256
`6d1641a9deb284be889ee6e2630a2be6e57cc5985c80af2c9da7d17543ed0785`.
The retained files are `01C5.html` and `01CR.html`.
As explained in `TensorRankOneStatement.md`, the target is the scheme
specialization of their consequence for nonnegative tensor powers.
The implemented proof uses local tensor closure directly.

The theorem concerns the recursively defined sheafified tensor powers,
including their trailing structure-sheaf factor. It covers nonnegative
exponents and imposes no affine, noetherian, quasi-compact, separated,
quasi-coherence or flatness hypotheses. It assumes no monoidal structure
on `LineBundle X` and proves no assertion about negative powers or tensor
inverses.
