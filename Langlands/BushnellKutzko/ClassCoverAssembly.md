# Covering simple-character classes: assembly of the reduction

* `SimpleCharacterFibreCharacterStatement` states `FibreCharacterAt` for every nonarchimedean local
  field `F`, finite-dimensional `V`, additive character `ψ_F` of `F` trivial on `𝔭_F` and nontrivial
  on `𝔬_F`, lattice chain `L`, and depth `k` with `k + 1 < n`. `FibreCharacterAt` concerns the
  quotient of two extensions; it is an auxiliary step of the proof of Lemma (2.7) of Bushnell and
  Kutzko, *Simple types in GL(N): computing conjugacy classes* (1994), printed p. 121, together with
  the remark on p. 120.
* `SimpleStratumScalarRefinementStatement` states `RefinementSimpleAt` (Bushnell and Kutzko,
  *The admissible dual of GL(N) via compact open subgroups* (1993), (2.2.8), (2.4.1); BK94 (1.8))
  for every finite-dimensional `V`, lattice chain `L` and depth `k` with `k + 1 < n`.
* `simpleCharacterFibreInjection_of` proves `SimpleCharacterFibreInjectionStatement` (BK94
  (2.7)–(2.10)) from these two statements and `PureStratumSimpleApproximationStatement`,
  `SimpleCharacterConjugationStatement`, `SimpleCharacterChoiceStatement`,
  `SimpleStratumGroupPropertiesStatement`, `SimpleCharacterRestrictionStatement`,
  `SimpleCharacterCoherenceStatement`, `SimpleCharacterTranslationStatement` and
  `SimpleCharacterCovarianceStatement`.
* `simpleCharacterClassCover_of` proves `SimpleCharacterClassCoverStatement` (BK94 (2.3), upper
  half) from the same hypotheses.

This module proves the target only under these hypotheses; it does not prove the hypotheses.
