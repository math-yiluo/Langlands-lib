# Localization of equivariant distributions along an invariant map

`Langlands.HarmonicAnalysis.Distribution.EquivariantLocalizationStatement.{uX, uY, uI}`
is the following proposition. This module defines the proposition and
supplies no proof of it; the separate published theorem
`Langlands.HarmonicAnalysis.Distribution.equivariantLocalization` proves it
(see [Status](#status)).

## Statement

Let `X : Type uX` be an arbitrary topological space and let `Y : Type uY` be a
Hausdorff, locally compact, totally disconnected topological space. Let
`q : X → Y` be continuous. Let `ι : Type uI` be an arbitrary index type, and
for each `i : ι` let `h i : X ≃ₜ X` be a homeomorphism and `χ i : ℂ` a scalar.
Assume that every `h i` preserves every fiber of `q`, that is,
`q (h i x) = q x` for all `i` and `x`.

Assume further, for every point `y : Y`: every distribution `T` on `X` that
is supported in the fiber `q ⁻¹ {y}` and satisfies `(h i)_* T = χ i • T` for
every `i` is zero. Here "supported in the fiber" is expressed without
restriction maps: `T f = 0` for every test function `f` that vanishes at every
point `x` with `q x = y`.

The conclusion is that every distribution `D` on `X` with
`(h i)_* D = χ i • D` for every `i` is zero.

The universes of `X`, `Y` and `ι` are independent. The family `h` need not form
a group, the scalars `χ i` are arbitrary complex numbers, and there is no
hypothesis on the fibers beyond the stated vanishing property. A fiber may be
empty; then the hypothesis for that point concerns distributions that vanish
on every test function.

## Exact meaning of the imported objects

`Distribution X` is the Library's `Module.Dual ℂ (SchwartzBruhat X)`: all
complex linear functionals on the locally constant, compactly supported
complex functions on `X`, with no continuity requirement. For a homeomorphism
`e`, the Library's `pushforward e` satisfies `(e_* D)(f) = D(f ∘ e)`, with no
measure factor. Thus `(h i)_* D = χ i • D` means `D(f ∘ h i) = χ i * D(f)` for
every test function `f`.

## Provenance

The registered original is Bernstein and Zelevinsky, *Representations of the
group GL(n,F), where F is a non-Archimedean local field (survey)* (1976),
`bernstein-zelevinsky-1976-representations-gln`, SHA256
`72dc22eb9991112936a88327f00d0f02a16a2bf8747518ca0ecfeeadd188e50c`.

Proposition 2.36 (printed p.25) and Corollary 2.37 (printed p.26) consider an
action of an l-group on an l-sheaf and a continuous invariant map `q : X → Y`
of l-spaces. They identify the stalks of the resulting sheaf on `Y` with the
fiber restrictions and conclude: if there are no invariant distributions on
any fiber `q⁻¹(y)`, there are none on `X`. Theorem 6.9 (printed p.54) uses
this corollary in its regular case.

The present proposition is an internal variant of Corollary 2.37 for the
constant sheaf of locally constant functions, designed for the proof of
`Langlands.GeneralLinearConjugationDistributionTransposeStatement`. It differs
from the source in these ways:

- Group invariance is replaced by equivariance under an arbitrary family of
  fiber-preserving homeomorphisms with arbitrary scalar factors. The
  published proof of the transpose statement takes the conjugations with
  factor `1` together with the transpose with factor `-1`.
- A distribution on the fiber is replaced by a distribution on `X` supported
  in the fiber, which avoids restriction maps to the fiber. When `X` is an
  l-space these are the same thing by the exact sequence of Proposition 1.8
  (printed p.7) and Corollary 1.9 (printed p.8).
- The space `X` is an arbitrary topological space; only `Y` carries the
  l-space hypotheses.

## Why the proposition is true

This sketch was written as the plan for the proof; this module does not
prove it. Let `N` be the linear span of the test functions `f ∘ h i - χ i • f`, and let
`I_y` be the test functions vanishing on `q ⁻¹ {y}`. A distribution vanishes on
`N` exactly when it satisfies all the equivariance identities. The fiber
hypothesis says that no nonzero linear functional vanishes on `N + I_y`, so
`N + I_y` is the whole test-function space.

Because `q ∘ h i = q`, the subspace `N` is stable under multiplication by
`φ ∘ q` for every locally constant `φ` on `Y`. Fix a test function `f` and a
point `y`, and write `f = n + g` with `n ∈ N` and `g ∈ I_y`. The support of `g`
is compact and open, and its image under `q` is a compact set not containing
`y`. As in the proof of Proposition 2.36, a compact open neighbourhood `V` of
`y` disjoint from that image exists. Then `(1_V ∘ q) • f = (1_V ∘ q) • n` lies
in `N`. Finitely many such `V` cover the compact set `q(supp f)`. Refining them
to a finite disjoint family of compact open sets and summing shows `f ∈ N`.
Hence every equivariant distribution is zero.

The published proof `equivariantLocalization` follows this algebraic
localization argument, with one difference: it does not refine the clopen
neighbourhoods to a disjoint family. It combines the finitely many cutoffs by
an inclusion–exclusion identity for the cutoff of a union instead.
[LocalizationProof](LocalizationProof.md) describes the implemented Lean
argument.

## Status

The proposition is proved by the theorem
`Langlands.HarmonicAnalysis.Distribution.equivariantLocalization.{uX, uY, uI}`
in `Langlands.HarmonicAnalysis.Distribution.LocalizationProof`. Its type is
exactly `EquivariantLocalizationStatement.{uX, uY, uI}`, with the same
independent universes and no added hypothesis. The proof is artifact
`8f3e3767-6c71-4b9e-a9f7-73744cd5d0f3` version 1. Its validation passed the
Lake build and exact-target checks, an independent review approved it, and it
was published at Library commit `d1e92cc3fedd601726630b19e4e6d1a9dc84b2cd`.
It proves only the localization stated here. It does not formalize the
l-sheaf statements Proposition 2.36 or Corollary 2.37 of
Bernstein–Zelevinsky.
