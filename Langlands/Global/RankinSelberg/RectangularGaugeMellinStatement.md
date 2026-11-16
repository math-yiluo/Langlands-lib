# Rectangular Mellin convergence for adelic simple-root gauges

`Langlands.Global.RankinSelbergGlobal.AdelicSimpleRootGaugeRectangularMellinStatement`
is an explicit, unproved proposition definition. It is an internal analytic
prerequisite for the unequal-rank rectangular Whittaker bound.

The field `F : Type u` has arbitrary universe, with instances `Field F`,
`NumberField F` and `CompactSpace (AdeleQuotient F)`. For every `r t : ℕ`
with `h : t < r` and every real `τ ≥ 0`, the proposition asks for a real
`C ≥ 0` such that, for every function `Ξ : Points F (r + 1) → ℝ≥0∞`
satisfying `IsAdelicSimpleRootGauge F r τ Ξ` and every real `σ > C`,

```text
∫⁻ p : WhittakerQuotient F (t + 1),
  (∫⁻ x, Ξ (rectangularPoint F h p.out x)
    ∂rectangleMeasure F (r - (t + 1)) (t + 1)) *
      ENNReal.ofReal (detNorm F (t + 1) p.out ^ σ)
  ∂whittakerQuotientMeasure F (t + 1) < ⊤.
```

The threshold may depend on the field, ranks and exponent `τ`. Its
existential quantifier precedes the quantifier over `Ξ`, so it is independent
of both the gauge and its defining Schwartz–Bruhat function. The proposition
asks for finiteness for each gauge; it supplies no common numerical bound
on the values of these integrals.

Write `n = r + 1` and `m = t + 1`. The published actual adelic point
`rectangularPoint F h g x` is the block matrix
`[[g,0,0],[x,I_(n-m-1),0],[0,0,1]]` in `GL_n(𝔸_F)`.
The variable `x` ranges over the entire matrix space
`Matrix (Fin (r - (t + 1))) (Fin (t + 1)) (Adeles F)`.
The two measures are the published `rectangleMeasure` on this Borel matrix
space and `whittakerQuotientMeasure` on the actual homogeneous space
`N_m(𝔸_F) \ GL_m(𝔸_F)`. The latter is the pushforward from the rational
unipotent quotient, as defined in `WhittakerIntegrals`.
The expression uses the published representative `p.out` and the normalized
idelic determinant norm `detNorm`; `^ σ` is the real power.
Both integrals are extended nonnegative lower integrals, so `< ⊤` expresses
finiteness directly, without the zero default of a nonintegrable Bochner
integral. The statement does not separately assert finiteness of the inner
integral at every representative.

All proper block sizes are retained, including `t = 0` and `t + 1 = r`.
In the latter case the rectangular matrix has zero rows; there is no
additional assumption that the rectangle is nonempty. The module imports
the generic `AdelicSimpleRootGauge` interface and is independent of
`UnequalGaugeReduction`. Whittaker functions, central determinant twists
and cuspidal realizations are not parameters of this proposition.

The source model is Jacquet, Piatetski-Shapiro and Shalika,
*Automorphic forms on GL(3) II* (1979), registered as `jps-1979-gl3-ii`.
Its §12.1, printed pages 226–227, defines gauges in general rank.
Lemma 13.4.3, printed pages 239–240 (scan pages 28–29), treats the
rank-three integral with matrix `[[a,0,0],[x,1,0],[0,0,1]]`
and weight `|a|^(s-1)`. For real `s` its weight corresponds to `σ = s-1`
here, with `r = 2` and `t = 0`. The proof factors the gauge into local
gauges, uses local convergence and unramified support, and reduces the
remaining product to Schwartz Mellin convergence.

Cogdell, *Analytic theory of L-functions for GL_n* (2004), registered as
`cogdell-2004-analytic-theory-gln`, §2.2, printed page 207 (PDF page 210),
displays the general-rank rectangular Whittaker integral and states its
absolute convergence in a right half-plane. That integral also contains
a smaller-rank Whittaker factor, which is absent here.
The proposition in this module is an internal general-rank, arbitrary-gauge
formulation motivated by this route. Neither cited passage is a literal
statement of this formulation with a threshold uniform over all defining
Schwartz–Bruhat functions. Establishing that uniform conclusion for the
Library's actual carriers and measures remains a separate analytic proof
obligation, requiring rectangular Iwasawa estimates, quotient integration
and global Schwartz–Bruhat Mellin/Euler product convergence. This module
proves neither that conclusion nor `UnequalRectGaugeStatement`.
