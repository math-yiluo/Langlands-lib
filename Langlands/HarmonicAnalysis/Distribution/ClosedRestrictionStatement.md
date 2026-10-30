# Restriction of Schwartz–Bruhat functions to closed subsets is surjective

`Langlands.HarmonicAnalysis.SchwartzBruhat.ClosedRestrictionSurjectiveStatement.{u}`
is the following proposition. This module defines the proposition and
supplies no proof of it; the separate published theorem
`Langlands.HarmonicAnalysis.SchwartzBruhat.closedRestrictionSurjective` proves
it (see [Status](#status)).

## Statement

Let `X : Type u` be a topological space in an arbitrary universe `u` that is
Hausdorff (`T2Space X`), locally compact (`LocallyCompactSpace X`) and totally
disconnected (`TotallyDisconnectedSpace X`). Let `Z : Set X` be a subset and
`hZ : IsClosed Z` a proof that it is closed. Then the published restriction map

```
SchwartzBruhat.restrictClosed hZ : SchwartzBruhat X →ₗ[ℂ] SchwartzBruhat Z
```

is surjective (`Function.Surjective`). In words: every locally constant,
compactly supported complex-valued function `g` on `Z` is the restriction of a
locally constant, compactly supported complex-valued function `f` on `X`, that
is, `f z.val = g z` for every `z : Z`.

The space `X`, its topology and the three topological properties, the subset
`Z` and the closedness proof `hZ` are all universally quantified inside the
proposition; nothing is fixed outside it. The universe `u` is the only
parameter of the definition.

## Exact meaning of the imported objects

`SchwartzBruhat X`, from `Langlands.HarmonicAnalysis.Basic`, is the subtype of
the complex submodule `schwartzBruhatSubmodule X` of `X → ℂ` consisting of the
functions that are locally constant (`IsLocallyConstant`) and have compact
support (`HasCompactSupport`). No
topology, norm or continuity condition beyond local constancy is involved.

`SchwartzBruhat Z` is the same space for the subtype `Z`, with Mathlib's
induced subtype topology. No other topology on `Z` is introduced.

`SchwartzBruhat.restrictClosed hZ`, from
`Langlands.HarmonicAnalysis.Distribution.Subspace`, is the published complex
linear map sending `f` to `f ∘ Subtype.val`; its evaluation law is
`restrictClosed_apply : restrictClosed hZ f z = f z.val`. That construction
needs only a topology on `X`; the Hausdorff, local compactness and total
disconnectedness hypotheses are added here only to assert surjectivity. The
imported modules are used unchanged.

## Scope

- No countability, sigma-compactness, group, group action, measure,
  representation, smoothness or manifold structure is assumed.
- Neither `X` nor `Z` is assumed compact or nonempty: the proposition covers
  empty `X`, the empty subset and `Z = X`. Only `X` carries topological
  hypotheses; `Z` is assumed only to be closed.
- No extension map, substitute function space or surjectivity premise is
  introduced; the surjectivity of the published map is the conclusion.
- The proposition says nothing about distributions. The resulting description
  of distributions supported on `Z` (the correspondence through
  `Distribution.closedPushforward`) and any orbit-vanishing theorem are not
  part of this unit.

## Provenance

This proposition is internal: it is formulated on existing Library objects as
the topological prerequisite for distributions supported on a closed subset,
and is not a transcription of a source statement.

The motivating passage is J. A. Shalika, *The multiplicity one theorem for
GL_n*, Ann. of Math. (2) 100 (1974), 171–193, registered as
`shalika-1974-multiplicity-one` (central file
`Shalika--The multiplicity one theorem for GLn--1974.pdf`, SHA256
`788c5d124024c768aa47c4e8b179475fbcf5b0882a518ae60b19cdc88089f087`).
Lemma 1.15 (printed p.178, PDF page 9) states that for a closed submanifold
`M₀` of a manifold `M` the restriction map from `C_c^∞(M)` to `C_c^∞(M₀)` is
surjective, and reduces the proof by a localization lemma to the inclusion of
coordinate spaces `k^{N₁} ⊂ k^{N₂}`. It follows Proposition 1.14, which
assumes the field `k` is non-archimedean, concerns a manifold `M` over `k`, and
uses in its proof that functions in `C_c^∞(M)` are locally constant. The
remark after Lemma 1.15 combines it with Proposition 1.14 to show, for
non-archimedean `k`, that a distribution on `M` with support in `M₀` is the
extension of a unique distribution on `M₀`.

The present proposition generalizes that lemma from closed submanifolds of a
manifold over a non-archimedean local field to arbitrary closed subsets of a
Hausdorff, locally compact, totally disconnected space. Its meaning does not
rely on the source's manifold structure or its proof by localization. No
errata for this passage are recorded in the project's notes.

## Proof route

This plan was written before the proof; this module does not prove it. A
function `g` in
`SchwartzBruhat Z` takes finitely many values, and each nonzero value is taken
on a compact open subset of `Z`. In `X`, compact open sets form a basis of the
topology, so each such subset is the trace on `Z` of a compact open subset of
`X`, obtained by covering it with finitely many compact open sets inside an
ambient open set whose trace on `Z` is that subset. Making these finitely many
ambient sets disjoint and taking the corresponding finite combination of their
indicator functions gives an extension of `g` that is zero outside a compact
open set.

The published proof `closedRestrictionSurjective` argues directly along these
lines, with one difference: it does not make the ambient compact clopen lifts
disjoint. They may overlap away from `Z`, which does not affect the
restriction. [ClosedRestrictionProof](ClosedRestrictionProof.md) describes the
implemented Lean argument.

## Consumers

The proposition is intended as the closed-restriction input for the Whittaker
multiplicity-one work (task `209cde88-bab8-4a85-8a9d-72b8864b6fa0`), the
Shalika distribution-invariance proof (task
`f79ca82c-d050-4ffa-821b-c347b60e36e0`) and the finite-orbit vanishing proof
(task `51a122ec-9363-4c38-9df9-593ffdb99219`). The published proofs
`Langlands.HarmonicAnalysis.Distribution.finiteOrbitAntiInvariantVanishing`
and `Langlands.HarmonicAnalysis.Distribution.closedSupportedDescent` use
`closedRestrictionSurjective`.

## Status

The proposition is proved by the theorem
`Langlands.HarmonicAnalysis.SchwartzBruhat.closedRestrictionSurjective.{u}` in
`Langlands.HarmonicAnalysis.Distribution.ClosedRestrictionProof`. Its type is
exactly `ClosedRestrictionSurjectiveStatement.{u}`, with no added hypothesis.
The proof is artifact `9f1d0056-dabe-4632-a2e4-dc0bcdf368e1` version 1. Its
validation passed the Lake build and exact-target checks, an independent review
approved it, and it was published at Library commit
`a2f65909d0470e0c9b71d24975a4fb12723f855f`. It proves only the surjectivity of
`restrictClosed hZ` stated here. The distribution consequences listed under
[Scope](#scope) are separate propositions.
