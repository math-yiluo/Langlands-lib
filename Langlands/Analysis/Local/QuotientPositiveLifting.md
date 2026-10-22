# Compact normalization and positive lifting for real quotient averages

Worker 101 proves the published propositions
`Langlands.QuotientIntegration.RealQuotientCompactNormalization` and
`Langlands.QuotientIntegration.RealQuotientPositiveLifting`, with closing theorems
`realQuotientCompactNormalization` and `realQuotientPositiveLifting` in the same
namespace. Their types are the original universal proposition definitions from
`Langlands.Analysis.Local.QuotientMeasurePrerequisites`, without added hypotheses.
The actual real averaging API is imported from
`Langlands.Analysis.Local.QuotientAverageReal`, authored by Worker 99.

## Scope and conventions

The group is an arbitrary locally compact Hausdorff topological group, in an
unrestricted universe, and the subgroup is closed. The subgroup has its induced
topology and a supplied Borel structure, with a regular Haar measure that is also
right invariant. The quotient is the existing `LeftQuotient H`, namely the
quotient by `QuotientGroup.rightRel H`. A representative `g` denotes the left
coset `H*g`, and the fiber integral is the actual real Bochner integral of
`h ↦ f(h.val*g)`. No countability assumption, ambient measure, quotient measure,
positive quotient functional, or lifting conclusion is an input.

The private lemma `quotient_mk_subgroup_mul` checks directly in the existing
quotient relation that `h.val*g` and `g` have the same image. It is an internal
algebraic identity used to pull quotient functions out of fiber integrals.

## Implemented compact normalization

For a compact quotient set `K`, the published topology theorem supplies a
compact subset `C` of the group whose image is exactly `K`. Mathlib's locally
compact Urysohn lemma supplies a continuous compactly supported real function
`b`, equal to one on `C` and valued in `[0,1]` everywhere.

Let `A` be the actual quotient average of `b`. Its continuity and fiber
integrability come from `QuotientAverageReal`. At a representative `x` in `C`,
the fiber function is nonnegative, continuous and integrable, and is one at the
identity of the subgroup. Haar measure is positive on nonempty open sets, so
`integral_pos_of_integrable_nonneg_nonzero` gives `A(q(x)) > 0`. Since `C`
surjects onto `K`, this proves positivity at every point of `K`.

Compactness and continuity now give a real number `ε > 0` with `ε ≤ A(q)` for
all `q ∈ K`, using `IsCompact.exists_forall_le'`. This lemma also covers the
empty compact set. Define

`f(g) = b(g) / max ε (A(q(g)))`.

The denominator is continuous and strictly positive everywhere. Thus `f` is
continuous and nonnegative, and its support is contained in the support of
`b`, proving compact support. The denominator is constant along each fiber,
so its average is `A(q(g)) / max ε (A(q(g)))`. For `q(g) ∈ K`, the maximum is
`A(q(g))`, which is positive, and this ratio is one. This proves the full
compact-normalization proposition.

## Implemented positive lifting

For a given real quotient test function `φ`, apply compact normalization to its
compact topological support, obtaining a nonnegative normalizer `b`. Define

`f(g) = φ(q(g)) * b(g)`.

Continuity follows by composition with the quotient projection and multiplication;
compact support follows from that of `b`. On a fiber, `φ(q(h*g)) = φ(q(g))`,
so the integral is `φ(q(g))` times the average of `b`. On the topological support
of `φ` this average is one. Outside that support `φ(q(g)) = 0`, so the same
identity holds there as well. If `φ` is nonnegative, both factors defining `f`
are nonnegative. This proves both clauses of the original positive-lifting
proposition, including the zero function case.

## Original source and proof variation

Gerald B. Folland, *A Course in Abstract Harmonic Analysis*, second edition
(2015), section 2.6: equation (2.47) and Lemma 2.48, printed page 61 / PDF page
74; Lemma 2.49 and Proposition 2.50, printed page 62 / PDF page 75. The retained
original PDF pages 74–76 were read. Registered source:
`folland-2015-abstract-harmonic-analysis-second`, SHA256
`c82467bfa77428c32d3e1a5d1cbdc11129511e0c61da2f9d8fbc717776b9e542`.

Folland averages `f(x*h)` on `xH` using left Haar measure. The project reverses
the convention to `f(h*x)` on `H*x`, so right invariance supplies independence
of representatives. The imported real averaging API implements this translation.

Folland's normalization proof uses an additional quotient cutoff and divides by
the average where that cutoff is supported. The implemented proof instead uses
a positive lower bound on the given compact set and the everywhere positive
maximum denominator described above. This is an internal proof variation that
establishes the same normalization conclusion. Positive lifting then follows by
the same product construction as Proposition 2.50. That proposition's additional
equality of support images is not part of the published target and is not
claimed here. This module proves no averaging-kernel or quotient-measure theorem.
