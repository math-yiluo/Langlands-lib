# The square-integrable Whittaker restriction-square estimate

Author: Worker 381.

This module defines the closed proposition
`Langlands.RankinSelberg.SquareIntegrableWhittakerRestrictionStatement.{uF,uV}`.
It states JPSS's restriction-square estimate, formula (7) on printed p.450:
for an irreducible square-integrable representation of the larger group,
every Whittaker function restricted to `diag(g, I_(r-t))` has integrable
square against `|det g|^(-(r-t))` on `N_t \ G_t`. It is a statement target,
not a proof.

## Quantifiers and hypotheses

Every prime `p`, field `F : PadicField.{uF} p`, supplied
`T : F.TopologicalData`, and pair `n k : ℕ` is quantified. The local
instances are exactly those of the published
`SquareIntegrableZeroRowAnalyticStatement`: `T.topology`, `T.valuativeRel`,
`T.localField`, and the Borel measurable structures (with their `BorelSpace`
proofs) on `F.Carrier`, on `GL_(n+1)(F)`, on its upper unipotent subgroup
`upperUnipotent (n + 1) F.Carrier`, and on
`LeftUnipotentQuotient n F.Carrier`. This is the p-adic specialization of
the source's non-Archimedean local-field setting; `T` need not be the
canonical choice.

Every `ψ : UnitaryAdditiveCharacter F.Carrier` is quantified; that structure
already includes continuity, nontriviality and unit-circle values. The
statement retains the explicit instance binder
`Measure.IsMulRightInvariant (unipotentHaar F.Carrier n)` and quantifies
every measure `μ` on `LeftUnipotentQuotient n F.Carrier` satisfying
`IsCompatible (upperUnipotent (n + 1) F.Carrier) (generalLinearHaar F.Carrier n)
(unipotentHaar F.Carrier n) μ`. Compatibility means `μ` is nonzero, regular,
invariant under right translation by `GL_(n+1)(F)`, and satisfies the Weil
quotient-integration formula, with integrability, for continuous compactly
supported complex functions on `GL_(n+1)(F)` relative to the published
normalized compact-open Haar measures `generalLinearHaar` and
`unipotentHaar`. No particular `μ` is chosen, and existence of a compatible
measure is neither asserted nor assumed.

The representation carrier `V : Type uV` has its own universe parameter and
only `AddCommGroup V` and `Module ℂ V`; no topology on `V` is used. The
representation is an actual
`π : Representation ℂ (Langlands.GeneralLinear (n + (0 + k + 1) + 1) F.Carrier) V`.
The hypotheses are exactly `Representation.IsIrreducible π` and the
published analytic predicate `T.IsSquareIntegrable π`. There is no
genericity, nonzero-functional, unitarization, Whittaker-norm integrability,
convergence, holomorphy, chosen-measure, or σ-finiteness hypothesis.

Every functional `ℓ : glFunctionals ψ (n + (0 + k + 1)) π` and every vector
`f : (coefficientModel π ℓ).toSubmodule` is quantified. Here
`glFunctionals` consists of all algebraic functionals with
`ℓ (π u v) = θ_ψ(u) ℓ v` for `u` in the upper unipotent subgroup of the large
group and its standard character `θ_ψ(u) = ψ(u_(1,2) + ⋯ + u_(r-1,r))`
(`standardCharacter`, the sum of the first superdiagonal entries), and
the coefficient model is the
image of `v ↦ (g ↦ ℓ (π g v))`, a space of `WhittakerFunctions ψ (n + (0 + k + 1))`.
For nonzero `ℓ` this is the source's Whittaker model `W(π; ψ)`; the
statement neither uses nor assumes uniqueness of Whittaker functionals.
Every vector of the admissible `π` is smooth, so the source's K-finiteness
of Whittaker functions is automatic in this p-adic setting.

## Ranks, quotient and integrand

Write the source ranks as

- `r = n + (0 + k + 1) + 1`, the rank of `π`'s group `G_r`;
- `t = n + 1`, the rank of the integration group `G_t = GL_(n+1)(F)`.

Then `r - t = 0 + k + 1 = k + 1 ≥ 1`. These rank expressions are kept
literally, matching `restrictedWhittakerNorm` and the zero-row
unequal-rank interfaces, so no rank cast or replacement representation is
needed. All values of `n` and `k` occur: `n = 0` gives `t = 1`, where
`N_1` is trivial and the quotient is `GL_1(F)`, and `k = 0` gives the
corank-one case `r - t = 1`, in which (7) is the source's formula (2) on
`N_(r-1) \ G_(r-1)`.

The quotient `LeftUnipotentQuotient n F.Carrier` is the space of left cosets
`N_t g`, that is the source's `N_t \ G_t`, with `N_t = upperUnipotent (n + 1)`.

The conclusion is

```lean
Integrable
  (fun q : LeftUnipotentQuotient n F.Carrier =>
    restrictedWhittakerNorm ψ k f.val q ^ 2 *
      quotientDeterminantAbs (normalizedAbsoluteValue T) n q ^
        (-(((0 + k + 1 : ℕ) : ℝ)))) μ
```

with the published constructions of
`Langlands.Representation.RankinSelberg.WhittakerNormData`:

- `restrictedWhittakerNorm ψ k f.val` takes the class of `g` to
  `‖f.val (appendIdentity n (0 + k + 1) g)‖` (`restrictedWhittakerNorm_mk`).
  The map `appendIdentity n (0 + k + 1)` is the diagonal inclusion
  `g ↦ diag(g, I_(k+1))` (`appendIdentity_entry`). Its square, a natural
  power of a real number, is the source's `|W|²[diag(g, 1)]`.
- `quotientDeterminantAbs (normalizedAbsoluteValue T) n` takes the class of
  `g` to `|det g|` for the normalized absolute value of `T`
  (`quotientDeterminantAbs_mk`). It is strictly positive
  (`quotientDeterminantAbs_pos`), so Mathlib's real power `x ^ (y : ℝ)` is
  the ordinary positive power. The exponent `-(((0 + k + 1 : ℕ) : ℝ))`
  equals `-(k + 1) = -(r - t)`.

Both functions are well defined on cosets: the norm removes the unitary
Whittaker character, and an upper unipotent matrix has determinant one.

`MeasureTheory.Integrable` is real-valued Bochner integrability with
respect to the supplied `μ`: almost-everywhere strong measurability and a
finite integral of the absolute value. Since the integrand is nonnegative,
this is the source's assertion "`< +∞`" together with measurability.

The statement makes no claim for other rectangular blocks and does not
contain the separate smaller-rank weighted-square estimate with a last-row
Schwartz cutoff, the second Cauchy–Schwarz factor.

## Original source

H. Jacquet, I. I. Piatetski-Shapiro and J. A. Shalika,
*Rankin–Selberg Convolutions*, American Journal of Mathematics 105 (1983),
367–464, Section 8.3, printed pp.448–451. Registered source
`jpss-1983-rankin-selberg`, SHA-256
`d9feed6388ca5acf02ecc6a8cce984871a7c28f062ff441e45a71fa2d8962245`,
retained at
`/home/taskhub/central-library/Jacquet-Piatetski-Shapiro-Shalika--Rankin-Selberg Convolutions--1983.pdf`.
The four pages were read visually from PDF pages 83–86 (one-based); the
scan has no text layer there. No registered errata for this source were
found in the project literature index or the public or project notes.

- p.448: the Proposition of (8.3), for square-integrable `π` and `σ`,
  states absolute convergence of `Ψ(s, W, W'; 0)` for `r > t` when
  `Re(s) > 0`.
- p.449: integration formula (1) over `N_r \ G_r`. Because Whittaker
  functions are K-finite and square-integrable modulo `N_r Z_r`, formula (2)
  gives `∫_{N_(r-1)\G_(r-1)} |W[diag(g, 1)]|² |det g|^(-1) dg = ‖W‖² < +∞`.
- p.450: for `r > t`, integration formula (6) over `N_(r-1) \ G_(r-1)`,
  with `g` in `N_t \ G_t`, `h` in `N_(r-t-1) \ G_(r-t-1)` and `k` in the
  maximal compact subgroup (printed `K_r`), shows that (2) implies (7):
  `∫_{N_t\G_t} |W|²[diag(g, 1)] |det g|^(-(r-t)) dg < +∞`.
  This unit formalizes (7). The same page introduces the zero-row integral.
- p.451: Cauchy–Schwarz bounds the square of the cut-off zero-row integral
  by the product of (7) and the smaller-rank integral; "the first by (7)"
  is finite.

The source's `dg` on `N_t \ G_t` is the invariant quotient measure; the
finiteness in (7) is unchanged by a positive rescaling of the measure.

## Square-integrability bridge

`T.IsSquareIntegrable π` is the published analytic predicate of
`Classification.Tempered`. For every Borel Haar measure on the actual
central quotient `GL_r(F) / Z`, it gives `IsSquareIntegrableModCenter`:
admissibility, a unitary central character, and `MemLp` with exponent two of
the norms of all matrix coefficients `g ↦ λ (π g v)` with `λ` in the smooth
dual. It is defined using smooth matrix coefficients modulo the center,
not Whittaker functions. The source's step to (2) instead uses
square-integrability of Whittaker functions modulo `N_r Z_r`.

Deriving that Whittaker square-integrability from matrix-coefficient
square-integrability, then (2) and the passage (6) ⟹ (7), together with all
bridges between the supplied topology, the Borel structures and the
compatible quotient measures, is a substantial future proof obligation. It
is not a hypothesis here. The statement does not replace
`T.IsSquareIntegrable` by a classification, Whittaker, tempered or
assumed-estimate predicate.

## Provenance and derived formulation

The proposition is the source's formula (7) for p-adic fields. The
following points are derived formulation, marked explicitly:

1. **Every compatible measure.** The source integrates against its
   invariant quotient measure. The statement quantifies every `μ` compatible
   with the published Haar measures, and retains the right-invariance
   instance binder for `unipotentHaar`, as in the published zero-row
   statement.
2. **Bochner integrability.** "`< +∞`" is formulated as `Integrable`, which
   also asserts almost-everywhere strong measurability of the integrand.
3. **Zero functionals and zero vectors.** The source works with nonzero
   Whittaker models. If `ℓ = 0`, then the coefficient model contains only the
   zero function, and the integrand is identically zero
   (`restrictedWhittakerNorm_zero`); similarly for `f = 0`. These elementary
   extensions are included rather than excluded.
4. **Literal rank expressions.** `r = n + (0 + k + 1) + 1` and `t = n + 1`
   are kept as written to match the published Whittaker norm data.

The statement is a prerequisite of the exact proof task for
`SquareIntegrableZeroRowAnalyticStatement`: it isolates the first square
factor of the Cauchy–Schwarz step on p.451.
