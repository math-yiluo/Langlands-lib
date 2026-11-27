# Reduction of Laumon's numerical statement E1b to the ℓ-adic statements

Module `Langlands.Correspondence.HenniartLaumonNumericalReductionStatement`,
namespace `Langlands.Henniart`. It imports
`Langlands.Correspondence.HenniartLadicStatement` and
`Langlands.Correspondence.HenniartLaumonNumericalStatement`, defines one
proposition and proves nothing.

## Statement

`LaumonNumericalReductionStatement.{uK, uW} : Prop` is the implication

```
LadicWeilOrbitComparisonStatement.{uK, uK, uW} →
  LaumonLadicTwistBijectionStatement.{uK, uW} →
    LaumonNumericalStatement.{uK, uW}
```

In words: suppose that

- **(orbit comparison)** for every nonarchimedean local field `K`, every
  separable closure `Ω` of `K`, every prime `ℓ` different from the residue
  characteristic of `K` (in Lean, `((ℓ : ℕ) : 𝓀[K]) ≠ 0`) and every ring
  embedding `ι : PadicAlgCl ℓ →+* ℂ`,
  there is an equivalence `e` from the unramified-twist orbits of irreducible
  ℓ-adic classes onto the unramified-twist orbits of continuous irreducible
  complex Weil classes, sending the orbit of an ℓ-adic class to the orbit of
  the Weil class underlying its transport, and with
  `e '' ladicRefinedStratum K Ω ℓ ι k s f = weilRefinedStratum K Ω k s f`
  for all `k s f : ℕ`
  (`Langlands.Henniart.LadicWeilOrbitComparisonStatement`,
  [module](HenniartLadicStatement.md));
- **(Laumon's bijection)** for every finite field `𝓀`, with
  `X = LaurentSeries 𝓀` and `Ω = SeparableClosure X`, every prime `ℓ` with
  `(ℓ : 𝓀) ≠ 0`, every `ι : PadicAlgCl ℓ →+* ℂ` and all `k s : ℕ` with
  `1 ≤ s`, there is one bijection from the irreducible ℓ-adic classes of
  rank `k + 1` and Swan exponent `s` (`LadicHasSwan X Ω ℓ ι ρ s`) onto those
  of rank `k + s + 1` and Swan exponent `s` that commutes with every
  unramified ℓ-adic twist
  (`Langlands.Henniart.LaumonLadicTwistBijectionStatement`,
  [module](HenniartLadicStatement.md)).

Then Laumon's numerical statement E1b holds
(`Langlands.Henniart.LaumonNumericalStatement`,
[module](HenniartLaumonNumericalStatement.md)): for every finite field `k`
and all `d s f : ℕ` with `1 ≤ s` and `f ∣ Nat.gcd (d + 1) s`, the refined
Weil strata
`weilRefinedStratum (LaurentSeries k) (SeparableClosure (LaurentSeries k)) d s f`
and `… (d + s) s f` have the same `encard`. In the notation of the route
note, `|W_X(n, s, f)| = |W_X(n + s, s, f)|` for `n = d + 1`.

The three propositions are used exactly as they are declared, by their Lean
names; none of them is restated, and no hypothesis is added. The implication
is a reduction: its two premises are named statements of the Library, and
this module proves neither of them.

## Universe levels

`LadicWeilOrbitComparisonStatement` declares the universe parameters
`uK uΩ uW` in this order: the field `K : Type uK`, its separable closure
`Ω : Type uΩ` and the representation carriers in `uW`. E1b concerns
`K = LaurentSeries k : Type uK` and `Ω = SeparableClosure (LaurentSeries k)`,
which also lives in `Type uK`, with carriers in `uW`; so the first premise is
used at `.{uK, uK, uW}`. `LaumonLadicTwistBijectionStatement` and
`LaumonNumericalStatement` both declare `uK uW` (the finite field `k` and the
carriers) and are used at `.{uK, uW}`. Both refined Weil strata in the
conclusion are `weilRefinedStratum.{uK, uK, uW}`, which is the stratum the
first premise compares at these universes.

## How the implication is proved

Fix a prime `ℓ` different from the characteristic of `k` (one of `2` and `3`
works) and an embedding `ι : PadicAlgCl ℓ →+* ℂ`; one exists, since
`PadicAlgCl ℓ` and `ℂ` are algebraically closed of characteristic zero and
both have the cardinality of the continuum, hence are isomorphic. A bijection
that commutes with every unramified twist maps twist orbits bijectively onto
twist orbits and preserves stabilizers, hence torsion numbers, so Laumon's
bijection matches `ladicRefinedStratum X Ω ℓ ι d s f` with
`ladicRefinedStratum X Ω ℓ ι (d + s) s f`; the orbit comparison, applied at
`K = X` (the residue field of `X` is isomorphic to `k`, so `(ℓ : k) ≠ 0`
gives its hypothesis that `ℓ` is nonzero there), is an equivalence that
carries both onto the two Weil strata, so their `encard` agree. This uses
`1 ≤ s` (a hypothesis of Laumon's bijection) and not the divisibility
`f ∣ Nat.gcd (d + 1) s`.

## Provenance

- Henniart (1988), §4.3, printed p. 510: Laumon's local Fourier transform
  `𝓕 = 𝓕^(0,∞')` ([Lm], 2.4.2.3), with `K = K'` and the same uniformizer
  on both sides, is an equivalence of the category of ℓ-adic representations
  onto its full subcategory of representations of slope `< 1`, with
  `s(𝓕(σ)) = s(σ)` and `n(𝓕(σ)) = n(σ) + s(σ)`, and is compatible with
  twisting by unramified ℓ-adic characters. The deduction concludes at the
  top of p. 511: "Pour tout entier `d ≥ 1` et tout entier `s ≥ 0`, on a donc
  une bijection entre `𝒢_K^{l,0}(d, s)` et `𝒢_K^{l,0}(d + s, s)`". Here
  `𝒢_K^{l,0}(d, s)` (§4.2, p. 510) is the set of unramified-twist orbits of
  ℓ-adic classes of dimension `d` and Swan exponent `s` whose restriction to
  inertia is irreducible, that is, of torsion number `1`. The passage between
  ℓ-adic and complex classes through classes of finite image is Henniart's
  §§4.1–4.2, pp. 509–510.
- The operator route note (`operator-numerical-llc-route-2026-11-16`,
  `numerical-LLC-route.tex`), Corollary `cor:Laumon` (lines 794–796), states
  the refined form `|W_{K'}(d, s, f)| = |W_{K'}(d + s, s, f)|` for all
  `f ∣ gcd(d, s)`, citing Henniart §4.3. Its proof (lines 797–802) first
  shows that the transform matches the irreducible representations of rank
  `d` and Swan conductor `s` with those of rank `d + s` and Swan conductor
  `s`; this bijection, with its compatibility with unramified twists, is
  `LaumonLadicTwistBijectionStatement`. Lines 799–802 then give the two
  steps of this reduction: "Compatibility with unramified twists gives a
  bijection of the sets of orbits that preserves stabilizers", and "the
  orbits of irreducible ℓ-adic representations of the Galois group and of
  irreducible complex representations of the Weil group under unramified
  twists correspond, with dimensions and conductors"; the form of this
  correspondence on refined strata (rank, Swan exponent and torsion number)
  is `LadicWeilOrbitComparisonStatement`.
- The source map
  [`notes/henniart/laumon-local-fourier-source-map.md`](../../notes/henniart/laumon-local-fourier-source-map.md),
  §1, steps (c) and (d): (c) assembles the twist-compatible bijection and
  derives the preservation of the torsion number from injectivity and twist
  compatibility; (d) passes from orbits of ℓ-adic Galois classes to orbits of
  complex Weil classes, preserving dimension, Swan conductor and torsion
  number. The proposition here is this sheaf-free endgame, with the hand-over
  statement of that section as its second premise.

The implication is a derived formulation of this deduction: the sources
work with `F_q((t))`, here `LaurentSeries k`; its two premises are the
statements of the Library named above; and the counts are refined by the
torsion number `f`, as in the route note's corollary, where Henniart's
conclusion concerns torsion number `1`.

## Sources

- G. Henniart, *La conjecture de Langlands locale numérique pour GL(n)*,
  Ann. Sci. ÉNS (4) 21 (1988), 497–544, `henniart-1988-numerical`; printed
  page = PDF page + 495. §§4.1–4.3, pp. 509–511 (PDF pp. 14–16). Retained PDF
  SHA-256 `3de93884b6c4b26106d614e648cfb7f293f9f40a66ef352c0751e222a602f25c`.
  [Henniart, pp. 510–511](https://www.numdam.org/article/ASENS_1988_4_21_4_497_0.pdf#page=15)
- *The numerical local Langlands correspondence for GL_n: counts on the two
  sides and the recommended route of proof* (16 November 2026),
  `operator-numerical-llc-route-2026-11-16`, `numerical-LLC-route.tex`,
  Corollary `cor:Laumon` and its proof, lines 794–802, and §2.2 (torsion
  numbers and refined strata), lines 182–203. Registered directory SHA-256
  `faece16e4d4722c37c1ba0e7ebba30a11d94b64639f20f19a6aa7ccff3faba3f`.
- [Laumon's local Fourier transform for E1b: source map](../../notes/henniart/laumon-local-fourier-source-map.md),
  §1.
