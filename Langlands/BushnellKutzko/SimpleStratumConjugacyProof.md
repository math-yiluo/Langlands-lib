# Proof of formal intertwining and conjugacy of simple strata

`Langlands.BushnellKutzko.simpleStratumConjugacy` proves the unchanged Library proposition
`Langlands.BushnellKutzko.SimpleStratumConjugacyStatement`, in the universes of the
statement. It applies `simpleStratumConjugacy_of_approximation`
(`SimpleStratumConjugacyReduction`) to `pureStratumSimpleApproximation`, the proof of
`PureStratumSimpleApproximationStatement` (BK93 (2.4.1)(i)).

Source: Bushnell–Kutzko, *The admissible dual of GL(N) via compact open subgroups* (1993),
registered as `bushnell-kutzko-1993-admissible-dual-gln`, (2.6.1), printed pp. 83–86
(PDF pp. 95–98), and (2.6.2), printed p. 86 (PDF p. 98).

## Structure of the proof

- `SimpleStratumConjugacyUnits`: no unit of `𝔄` is conjugate into `𝔓`; hence the case of
  equal orders and levels of (2.6.2) (`conj_not_mem_of_isPure`).
- `SimpleStratumConjugacyResidual`, `SimpleStratumConjugacyCyclic`,
  `SimpleStratumConjugacyDepthOne`: the case `t = n − 1` for pure strata, by residual
  polynomials and a comparison of two cyclic splitting bases, and the final pure-or-null
  case analysis of the induction step.
- `SimpleStratumConjugacyRelative`, `SimpleStratumConjugacyStep`: the induction step,
  using (1.5.8), (2.4.1)(i), (ii)(c), (iii) and (2.2.1), with the derived cosets compared
  over `E = F[γ]` regarded as a local field.
- `SimpleStratumConjugacyReduction`: the induction on `t` and both clauses of the
  statement.
