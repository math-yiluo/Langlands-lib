# Finite-rank transpose and image-containing restrictions

This module extends the genuine finite-rank trace API on an arbitrary complex
vector space `V : Type uV`. It assumes only `AddCommGroup V` and `Module ℂ V`;
there is no topology or ambient finite-dimensionality hypothesis.

## Restriction containing the entire image

For `T : finiteRankEnd V`, a submodule `S` and `hS : T.val.range ≤ S`,
`FiniteRankEnd.restrict T S hS` is the actual restriction of `T` to `S`,
bundled as a finite-rank endomorphism of `S`. It factors through `T.val.range`:
first apply `T` to a vector of `S`, then include its value from the range into
`S`. The range is finite-dimensional by the original finite-rank hypothesis.
Thus `ofFactorization` supplies finite rank without assuming that `S` is
finite-dimensional.

`restrict_coe` identifies the underlying operator with `onSubspace T.val S hS`,
and `restrict_apply` identifies its value in `V` with `T.val v`.
For `trace_restrict`, the finite-dimensional factorization formula computes
the trace on the original range of `T`. The reversed composite is exactly
`T` restricted to that range, so this value is definitionally `trace T`.

Full-image containment is essential. Mere invariance of a subspace does not
imply equality of traces: the restriction of a nonzero rank-one projection to
the zero subspace has trace zero.

## Actual algebraic transpose

Write `R = T.val.range`, `q : V →ₗ[ℂ] R` for the range restriction of `T`, and
`i : R →ₗ[ℂ] V` for inclusion. Then `T = i ∘ q`.
`FiniteRankEnd.transpose T` is constructed as `q.dualMap ∘ i.dualMap`, factoring
through the finite-dimensional space `Module.Dual ℂ R`. Its underlying operator
is the actual `T.val.dualMap`, as proved by `transpose_coe`; `transpose_apply`
says its value on a functional `ℓ` at a vector `v` is `ℓ (T.val v)`.

For `trace_transpose`, the finite-rank factorization formula gives the ordinary
trace on `Module.Dual ℂ R` of `i.dualMap ∘ q.dualMap`. This is the transpose of
`q ∘ i`, the restriction of `T` to its original range. Mathlib's
`LinearMap.trace_transpose'`, applied to this finite-dimensional space, gives
the ordinary trace on `R` of that restriction. This is the definition of the
original genuine finite-rank trace. Ambient trace on `V` or its full dual is
never substituted for a genuine finite-rank trace.

## Restricted transpose

For a submodule `S` of `Module.Dual ℂ V` and the explicit hypothesis
`T.val.dualMap.range ≤ S`, `transposeOn T S hS` restricts the actual finite-rank
transpose to `S`. The underlying-operator and evaluation identities are
`transposeOn_coe` and `transposeOn_apply`. In particular the functional
represented by the output sends `v` to `ℓ.val (T.val v)`.

`trace_transposeOn` combines `trace_restrict` with `trace_transpose`.
It proves equality with the original trace even when `S` is infinite-dimensional.
The construction does not prove the full-image-containment hypothesis for any
particular representation or integrated Hecke operator. Preservation of smooth
functionals alone does not supply that hypothesis.

## Source and derived provenance

The intended application is the trace step in Bernstein and Zelevinsky,
*Representations of the group GL(n,F), where F is a non-Archimedean local field
(survey)* (1976), Theorem 7.3, printed/PDF page 57. The source explicitly uses
finite rank and containment of the transpose image in the smooth dual to compare
the restricted transpose trace with the original trace. The registered source
is `bernstein-zelevinsky-1976-representations-gln`, SHA256
`72dc22eb9991112936a88327f00d0f02a16a2bf8747518ca0ecfeeadd188e50c`, retained at
`/home/taskhub/central-library/Bernstein-Zelevinsky--Representations of the group GL(n,F) where F is a non-archimedean local field (survey)--1976.pdf`.

The general submodule constructions and implemented finite-stage proofs are
derived internally from `Langlands.LinearAlgebra.FiniteRankTrace` and Mathlib's
finite-dimensional dual and trace APIs. They make the source's algebraic trace
step reusable without asserting its separate representation-theoretic
image-containment premise, a smooth-dual character formula, or a
Gelfand–Kazhdan equivalence.
