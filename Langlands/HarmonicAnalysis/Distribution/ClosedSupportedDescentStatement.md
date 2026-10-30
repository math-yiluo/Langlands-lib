# Unique descent of distributions supported on a closed subset

`Langlands.HarmonicAnalysis.Distribution.ClosedSupportedDescentStatement.{u}`
is the following proposition. This module defines the proposition and
supplies no proof of it; the separate published theorem
`Langlands.HarmonicAnalysis.Distribution.closedSupportedDescent` proves it
(see [Status](#status)).

## Statement

Let `X : Type u` be a topological space in an arbitrary universe `u` that is
Hausdorff (`T2Space X`), locally compact (`LocallyCompactSpace X`) and totally
disconnected (`TotallyDisconnectedSpace X`). Let `Z : Set X` be a subset and
`hZ : IsClosed Z` a proof that it is closed. Then the published complex linear
map

```
Distribution.closedPushforwardSupported hZ :
  Distribution Z →ₗ[ℂ] Distribution.supportedOn Z
```

is bijective (`Function.Bijective`).

In words, for every algebraic distribution `T` on `X` such that `T f = 0`
for every test function `f` on `X` with `f z = 0` for all `z ∈ Z`, there is
exactly one algebraic distribution `D` on `Z` such that

```
T f = D (SchwartzBruhat.restrictClosed hZ f)   for every f : SchwartzBruhat X.
```

Surjectivity gives existence of `D`; injectivity gives its uniqueness.

The space `X`, its topology and the three topological properties, the subset
`Z` and the closedness proof `hZ` are all universally quantified inside the
proposition; nothing is fixed outside it. The universe `u` is the only
parameter of the definition.

## Exact meaning of the imported objects

`SchwartzBruhat X`, from `Langlands.HarmonicAnalysis.Basic`, is the complex
vector space of functions `X → ℂ` that are locally constant
(`IsLocallyConstant`) and have compact support (`HasCompactSupport`).
`Distribution X`, from `Langlands.HarmonicAnalysis.Distribution.Basic`, is its
full algebraic dual `Module.Dual ℂ (SchwartzBruhat X)`: every complex linear
functional, with no topology or continuity condition. `SchwartzBruhat Z` and
`Distribution Z` are the same constructions for the subtype `Z`, with
Mathlib's induced subtype topology. No other topology on `Z` is introduced.

The remaining objects are published in
`Langlands.HarmonicAnalysis.Distribution.Subspace`:

- `SchwartzBruhat.restrictClosed hZ : SchwartzBruhat X →ₗ[ℂ] SchwartzBruhat Z`
  sends `f` to `f ∘ Subtype.val`.
- `Distribution.supportedOn Z` is the complex submodule of `Distribution X`
  consisting of those `T` with `T f = 0` for every `f : SchwartzBruhat X`
  such that `f z = 0` for all `z ∈ Z` (membership law
  `Distribution.mem_supportedOn_iff`). This is support by pointwise
  annihilation, not support defined through open restrictions or a
  topological support of a distribution.
- `Distribution.closedPushforward hZ` is the dual map of `restrictClosed hZ`,
  so `closedPushforward hZ D f = D (restrictClosed hZ f)`.
- `Distribution.closedPushforwardSupported hZ` is that same map with its
  codomain restricted to `supportedOn Z`, using
  `closedPushforward_mem_supportedOn`; its coercion law is
  `coe_closedPushforwardSupported`.

The proposition asserts bijectivity of this existing map. It does not assert
the existence of some other linear equivalence between these spaces. The
imported modules are used unchanged.

## Scope

- No countability, second countability, sigma-compactness, group, group
  action, measure, representation, smoothness or manifold structure is
  assumed, and no topology or continuity condition is placed on
  distributions.
- Neither `X` nor `Z` is assumed compact or nonempty: the proposition covers
  empty `X`, the empty subset and `Z = X`. Only `X` carries topological
  hypotheses; `Z` is assumed only to be closed.
- No premise asserts surjectivity of `restrictClosed hZ`, an extension
  operator, an ambient support theorem or the desired bijection. The separate
  proposition `SchwartzBruhat.ClosedRestrictionSurjectiveStatement` in
  `Langlands.HarmonicAnalysis.Distribution.ClosedRestrictionStatement` is not
  imported or assumed here.
- Locally closed restriction, orbit vanishing, invariance under group
  actions and Whittaker or Shalika multiplicity statements are not part of
  this unit.

## Provenance

This proposition is internal: it is formulated on existing Library objects as
the common descent interface for distributions supported on a closed subset,
and is not a transcription of a source statement.

The motivating passage is J. A. Shalika, *The multiplicity one theorem for
GL_n*, Ann. of Math. (2) 100 (1974), 171–193, registered as
`shalika-1974-multiplicity-one` (central file
`Shalika--The multiplicity one theorem for GLn--1974.pdf`, SHA256
`788c5d124024c768aa47c4e8b179475fbcf5b0882a518ae60b19cdc88089f087`), printed
p.178, PDF page 9. There Proposition 1.14 assumes a non-archimedean field
`k`, a manifold `M` over `k` and a closed subset `C`, and states that a
distribution `T₁` on `M` with support in `C` vanishes on every `f` in
`C_c^∞(M)` vanishing on `C`. Lemma 1.15 states that for a closed submanifold
`M₀` of `M` the restriction map from `C_c^∞(M)` to `C_c^∞(M₀)` is surjective.
The remark that follows says that, for non-archimedean `k`, these two results
imply that a distribution `T₁` with support in `M₀` is the extension
(co-restriction) to `M` of a unique distribution on `M₀`.

The present proposition generalizes that remark in two ways. It replaces a
closed submanifold of a manifold over a non-archimedean field by an arbitrary
closed subset of a Hausdorff, locally compact, totally disconnected space.
It also takes support in the pointwise-annihilator sense above, which is the
conclusion of Proposition 1.14 rather than the source's usual
distribution-theoretic support. Its meaning does not rely on the source's
manifold structure. No errata file for this source is recorded in the
project's literature pointers or notes.

## Proof route

This plan was written before the proof; this module does not prove it. It
combines two observations, as in the source remark. Surjectivity of closed test-function restriction for such `X` gives
injectivity: if `D ∘ restrictClosed hZ = 0`, then `D` vanishes on every test
function on `Z`. For surjectivity, given `T` in `supportedOn Z`, define `D g`
as `T f` for any extension `f` of `g`; two extensions differ by a function
vanishing on `Z`, which `T` annihilates, so `D` is well defined and linear.
Restriction surjectivity is the content of the separate statement
`SchwartzBruhat.ClosedRestrictionSurjectiveStatement`.

The published proof `closedSupportedDescent` follows this route. It proves
bijectivity from surjectivity of `restrictClosed hZ` by Mathlib's dual-map
and quotient constructions, then supplies that surjectivity with the
published theorem `SchwartzBruhat.closedRestrictionSurjective`.
[ClosedSupportedDescentProof](ClosedSupportedDescentProof.md) describes the
implemented Lean argument.

## Consumers

The proposition was requested as a common interface by Worker 634 for the
Shalika distribution-invariance task
`f79ca82c-d050-4ffa-821b-c347b60e36e0`, and is intended for the Whittaker
multiplicity-one work of Worker 16 (task
`209cde88-bab8-4a85-8a9d-72b8864b6fa0`).

## Status

The proposition is proved by the theorem
`Langlands.HarmonicAnalysis.Distribution.closedSupportedDescent.{u}` in
`Langlands.HarmonicAnalysis.Distribution.ClosedSupportedDescentProof`. Its
type is exactly `ClosedSupportedDescentStatement.{u}`, with no added
hypothesis. The proof is artifact `9f406413-d230-4c0b-a1fa-239bd99494c7`
version 1. Its validation passed the Lake build and exact-target checks, an
independent review approved it, and it was published at Library commit
`00be69b7f127e77ee2fd0511ffe34c48595b64d4`. It proves only the bijectivity
stated here. The locally closed, orbit-vanishing, invariance and
multiplicity statements listed under [Scope](#scope) are not consequences of
this unit.
