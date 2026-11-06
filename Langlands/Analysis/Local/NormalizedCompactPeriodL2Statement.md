# Normalized compact quotient periods of L² vectors

`Langlands.QuotientIntegration.NormalizedCompactPeriodL2Statement`
gives convergence, compact test forms and closedness for the actual
normalized character period defined in `CompactQuotientPeriod`.
The ambient and period groups have independent universes.

The ambient group `G` is locally compact, Hausdorff, second countable
and Borel, with an actual left Haar measure `μ`. The integration
measure on `G` is its actual inverse right measure `μ.inv`. A closed
subgroup `Γ` has an actual s-finite right-invariant measure finite on
compact sets. The actual quotient measure `ν` is finite on compact
sets and satisfies the existing `IsCompatible Γ μ.inv μΓ ν`.

The period group `H` has the same topological and Borel hypotheses.
Its discrete subgroup `Λ` has a Borel actual left quotient. The
actual nonzero measure `μH` is `Λ`-invariant and finite on compact
sets. An actual compact set `K` meets every left `Λ` orbit. A
continuous homomorphism `j : H →* G` maps `Λ` into `Γ`, and a
continuous character `χ : H →* ℂˣ` is trivial on `Λ`. Character
unitarity, normality and unimodularity are not assumptions.

Write `νH` for the existing `normalizedMeasure` on `Λ \ H` using
the canonical Borel domain, and `P` for the corresponding actual
`normalizedQuotientCharacterPeriod`. The conclusion asserts:

- For every actual `φ : Lp ℂ 2 ν`, its character-period integrand
  is absolutely integrable for almost every `g` with respect to
  `μ.inv`, and `P φ` is locally integrable on `G`.
- For every actual `f : C_c(G, ℂ)`, there is a continuous complex
  linear form `ℓ` on this L² space such that `star(f) * P φ` is
  absolutely integrable for every `φ`, and its integral equals
  `ℓ φ`.
- The set of L² vectors whose actual period vanishes almost
  everywhere on `G` is closed.

This is an internal continuous formulation of the compact-period
argument in Getz–Hahn, *An Introduction to Automorphic
Representations* (2024), §9.2, (9.7), Lemmas 9.2.3–9.2.6 and
Proposition 9.2.2, printed pp. 243–246 (PDF pp. 255–258). The
October 2026 errata corrects the period quotient after (9.9) and
the character/modular factor in Lemma 9.2.6. The implementation
retains the actual `Delta(j(h))` factor before cancellation.
With conjugate-first Hilbert pairing and `c(h) = χ(h)⁻¹`,
the auxiliary weight is `star(c(h) / Delta(j(h)))`.

The actual relatively compact Borel-domain refinement, product
integrability under right-Haar change of variables, normalized
quotient integration, local integrability and compact continuous
test separation supply the argument. No bounded unsmoothed
evaluation on L², supplied period convergence, or supplied
continuous period forms replace these conclusions.

Application to every actual rational parabolic radical on the
positive split-centre adelic quotient still requires the exact
orbit, character and canonical-measure comparison. The source's
literal smooth test-space comparison remains separate, as do the
all-parabolic cuspidal identification, smoothing and spectral
theorems. This target asserts the concrete period-vanishing
closedness above.
