# Scalar covariance of supported descent through an open subspace

`Langlands.HarmonicAnalysis.Distribution.supportedDescentCovariance.{u}`
proves exactly the published proposition
`Langlands.HarmonicAnalysis.Distribution.SupportedDescentCovarianceStatement.{u}`
from [SupportedDescentCovarianceStatement](SupportedDescentCovarianceStatement.md).
Let `X : Type u` be Hausdorff, locally compact and totally disconnected. Let
`U ⊆ X` be open and let `Z ⊆ X` be any subset whose preimage
`Z_U = (Subtype.val : U → X) ⁻¹' Z` is closed in `U`. Let `D` be any
distribution in the actual submodule `supportedOn Z`. Let `e : X ≃ₜ X`,
`eU : U ≃ₜ U` and `eZ : Z_U ≃ₜ Z_U` be homeomorphisms with
`(eU x).val = e x.val` for every `x : U` and `(eZ z).val = eU z.val` for
every `z : Z_U`, and let `c : ℂ` be any scalar, including zero. If
`pushforward e D = c • D`, then the published chosen descent satisfies
`pushforward eZ (descendInOpen hU hZU D) = c • descendInOpen hU hZU D`.
The convention is the published one: `pushforward e T` evaluates `T` on
`pullback e f`, the test function `f ∘ e`.

## Two naturality lemmas

The module first proves two equalities of test functions. They are placed
in the `Langlands.HarmonicAnalysis.SchwartzBruhat` namespace.

`SchwartzBruhat.extendZero_pullback` assumes only a Hausdorff space `X`, an
open `U`, homeomorphisms `e` of `X` and `eU` of `U` with
`(eU x).val = e x.val` for all `x : U`, and a test function `f` on `U`. It
states `extendZero hU (pullback eU f) = pullback e (extendZero hU f)`. The
proof compares values at each `x : X`. If `x ∈ U`, the published formula
`extendZero_apply_subtype` evaluates the left side at `⟨x, hx⟩` to
`f (eU ⟨x, hx⟩)`. The compatibility premise rewrites `e x` as
`(eU ⟨x, hx⟩).val`, and the same formula evaluates the right side to the same
value. If `x ∉ U`, then `e x ∉ U` too. Otherwise `y = ⟨e x, _⟩` would lie in
`U`, and the compatibility premise applied to `eU.symm y` gives
`e (eU.symm y).val = e x`. Injectivity of `e` then gives
`(eU.symm y).val = x`, which would put `x` in `U`. Both sides are therefore
zero by `extendZero_apply_of_not_mem`.

`SchwartzBruhat.restrictClosed_pullback` assumes a topological space `Y`, a
closed `Z ⊆ Y`, homeomorphisms `e` of `Y` and `eZ` of `Z` with
`(eZ z).val = e z.val`, and a test function `f` on `Y`. It states
`restrictClosed hZ (pullback e f) = pullback eZ (restrictClosed hZ f)`. Both
sides evaluate at `z` to `f` of a point, namely `f (e z.val)` and
`f (eZ z).val`. These agree by the compatibility premise.

Neither lemma assumes that any subset is stable under the ambient map. The
compatibility premises supply this stability.

## Main proof

The open subtype `U` is locally compact by Mathlib's
`IsOpen.locallyCompactSpace`. As a subspace it is also Hausdorff and totally
disconnected. Two distributions on `Z_U` are equal if they agree on every
test function `φ`. The published theorem
`SchwartzBruhat.closedRestrictionSurjective`, applied in the space `U` to the
closed subset `Z_U`, writes `φ = restrictClosed hZU f` for some test function
`f` on `U`. Unfolding `pushforward` turns the goal into

`descendInOpen hU hZU D (pullback eZ (restrictClosed hZU f)) =
c • descendInOpen hU hZU D (restrictClosed hZU f)`.

`restrictClosed_pullback`, with `eU`, `eZ` and the second compatibility
premise, moves `pullback eZ` inside as `restrictClosed hZU (pullback eU f)`.
The published characterization `descendInOpen_apply_restrictClosed`, from
[SupportedRestriction](SupportedRestriction.md), turns both evaluations of
the descent into ambient evaluations. The goal becomes
`D (extendZero hU (pullback eU f)) = c • D (extendZero hU f)`.
`extendZero_pullback`, with `e`, `eU` and the first compatibility premise,
rewrites the left argument as `pullback e (extendZero hU f)`. The goal is now
the ambient premise `pushforward e D = c • D` evaluated at
`extendZero hU f`, and the proof closes with this evaluation.

The argument uses only algebraic linearity of the full complex algebraic
duals and the actual chosen `descendInOpen`. It uses no continuity of
distributions, measure or group structure. It assumes neither closedness of
`Z` in `X` nor stability of `Z` under `e`. The cases where the scalar is zero
or a space is empty need no separate treatment.
The theorem has no premise beyond those of the target, so its type is
exactly `SupportedDescentCovarianceStatement.{u}`, with the universe
arbitrary. The target statement and all imported Lean and Markdown pairs are
unchanged. The module imports the published statement and
`Distribution.ClosedRestrictionProof`, and nothing private.

## Provenance and authorship

This is an internal deduction from published Library constructions. These
are the Schwartz–Bruhat maps `restrictClosed` and `extendZero`, the
transport `pullback` and `pushforward`, `supportedOn` and `descendInOpen`.
No literature statement is transcribed. Worker 634 wrote the proof as the
private `SupportedDescentCovarianceCore` module of the shared Shalika task
draft (task `f79ca82c-d050-4ffa-821b-c347b60e36e0`, revision 8). Worker 1079
ported the two helpers and the final proof into this production module. The
port made only two changes: the public target replaces the private design
statement, and the helpers moved into the `SchwartzBruhat` namespace. The
proof steps are the same. The extension/restriction naturality strategy
adapts Worker 33's published algebraic helpers `extension_pullback` and
`restriction_pullback` in
[FiniteOrbitVanishingProof](FiniteOrbitVanishingProof.md). Those helpers
assume a single ambient homeomorphism that preserves the subset. Here the
helpers use the actual named extension and restriction maps, and they allow
independently specified compatible homeomorphisms on each space.
