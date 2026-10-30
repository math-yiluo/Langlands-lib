# Anti-invariant distributions on homogeneous spaces vanish

`Langlands.HarmonicAnalysis.Distribution.HomogeneousAntiInvariantVanishingStatement.{uG, uX}`
is the following proposition. This module defines the proposition and
supplies no proof of it; the separate published theorem
`Langlands.HarmonicAnalysis.Distribution.homogeneousAntiInvariantVanishing`
proves it (see [Status](#status)).

## Statement

Let `G : Type uG` be a group with a topology making it a nonarchimedean
topological group (Mathlib's `NonarchimedeanGroup`: a topological group in
which every neighbourhood of `1` contains an open subgroup). Assume `G` is
locally compact and sigma-compact. Let `X : Type uX` be a Hausdorff, locally
compact topological space with an action of `G` that is jointly continuous
(`ContinuousSMul G X`) and transitive (`MulAction.IsPretransitive G X`).

Let `σ : X ≃ₜ X` be any homeomorphism and `D` a distribution on `X`. If
`(g •)_* D = D` for every `g : G`, where `g •` is the homeomorphism
`Homeomorph.smul g`, and `σ_* D = -D`, then `D = 0`.

No relation between `σ` and the action is assumed, and `X` may be empty. The
universes of `G` and `X` are independent.

## Exact meaning of the imported objects

`Distribution X` is the Library's `Module.Dual ℂ (SchwartzBruhat X)`: all
complex linear functionals on the locally constant, compactly supported
complex functions on `X`, with no continuity requirement. For a homeomorphism
`e`, `pushforward e` satisfies `(e_* D)(f) = D(f ∘ e)`. So the hypotheses say
`D(f ∘ (g •)) = D(f)` for all `g` and `f`, and `D(f ∘ σ) = -D(f)` for all `f`.

## Provenance

The registered original is Bernstein and Zelevinsky, *Representations of the
group GL(n,F), where F is a non-Archimedean local field (survey)* (1976),
`bernstein-zelevinsky-1976-representations-gln`, SHA256
`72dc22eb9991112936a88327f00d0f02a16a2bf8747518ca0ecfeeadd188e50c`.

Example 6.12 (printed p.56) verifies condition d) of Theorem 6.10 on a single
orbit `S` with one-dimensional stalks. Every nonzero invariant distribution
on `S` is proportional to a positive distribution `T₀` given by integration
over `H\G`. Condition b) of Theorem 6.10 makes `σT₀` invariant, so
`σT₀ = c · T₀`. The source observes that `c = 1` holds, for example, when `σ`
fixes the base point `s` and acts on its stalk by a positive number: then `c`
is positive because `T₀` is, and condition c) gives `c^n = 1`.
Section 7.3 (printed pp.57–58) needs exactly this on each conjugacy class,
where it applies Theorem 6.13 (printed p.56) with `σ` equal to transpose.

The present proposition is an internal, Haar-measure-free form of this
positivity argument. It is designed for the proof of
`Langlands.GeneralLinearConjugationDistributionTransposeStatement`. It is not
a verbatim source statement:

- It asserts only that a `σ`-anti-invariant invariant distribution vanishes.
  This is the special case of the conclusion `σT = T` that the published
  proof of the transpose statement needs after replacing `T` by
  `T - σ_* T`.
- It assumes nothing about `σ`. The source needs condition b) of Theorem 6.13
  to make `σ_* T` again invariant; here that invariance is part of the
  hypotheses on `D`.
- It does not identify the invariant distributions on `X` with measures.

## Why the proposition is true

This sketch was written as the plan for the proof; this module does not
prove it. Fix `x : X`. By Mathlib's `isOpenMap_smul_of_sigmaCompact`, the orbit map
`g ↦ g • x` is open, so for every compact open subgroup `K` of `G` the set
`K • x` is compact and open. These sets form a neighbourhood basis at `x`,
and translating them gives one at every point. In particular `X` is totally
disconnected, and every test function is a finite linear combination of
indicators of compact open sets.

If `K' ≤ K` are compact open subgroups with `K'` normal in `K`, then `K • x` is
the disjoint union of finitely many translates `k • (K' • x)`. By invariance
`D(1_{K • x}) = N * D(1_{K' • x})` for a positive integer `N`. Using normal
cores of finite-index subgroups, any two values `D(1_{K₁ • x})` and
`D(1_{K₂ • x})` are positive rational multiples of a common value. Every
nonempty compact open `U ⊆ X` is a finite disjoint union of translates of sets
`L • x`. Hence `D(1_U) = r_U * a` for a positive rational `r_U` and a fixed
complex number `a`.

Apply this to `U = σ ⁻¹ (K • x)`. The identity `σ_* D = -D` gives
`r_U * a = -a`, so `(r_U + 1) * a = 0` and `a = 0`. Then `D` vanishes on every
indicator of a compact open set, hence on every test function.

The published proof `homogeneousAntiInvariantVanishing` follows this
argument. The positive rational comparison of indicator values is the
separate proposition `HomogeneousIndicatorProportionalityStatement`, proved
by the published theorem `homogeneousIndicatorProportionality`, and the
anti-invariance step is then a short algebraic deduction.
[HomogeneousVanishingProof](HomogeneousVanishingProof.md) describes the
implemented Lean argument.

## Status

The proposition is proved by the theorem
`Langlands.HarmonicAnalysis.Distribution.homogeneousAntiInvariantVanishing.{uG, uX}`
in `Langlands.HarmonicAnalysis.Distribution.HomogeneousVanishingProof`. Its
type is exactly `HomogeneousAntiInvariantVanishingStatement.{uG, uX}`, with
the same independent universes and no added hypothesis. The proof is artifact
`0dcd54e0-fdea-4fd5-a15c-904ca2bb3ec0` version 1. Its validation passed the
Lake build and exact-target checks, an independent review approved it, and it
was published at Library commit `914d13e3395c5a4417f36ffd7646c45c721a4b3e`.
It proves only the vanishing stated here. It does not identify invariant
distributions with measures or prove Example 6.12 of Bernstein–Zelevinsky.
