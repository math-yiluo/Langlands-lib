# Elliptic pseudo-coefficients of supercuspidal representations from cusp-form descent

The module `Langlands.BaseChange.SupercuspidalEllipticPseudoCoefficientReduction` states and
proves the implication

`SupercuspidalEllipticPseudoCoefficientReductionStatement.{u, uV, uW} :=
  CuspFormOrbitalVanishingStatement.{u} → SupercuspidalEllipticPseudoCoefficientStatement.{u, uV, uW}`

by the theorem `supercuspidalEllipticPseudoCoefficientReduction.{u, uV, uW}`.

## The two propositions

- `CuspFormOrbitalVanishingStatement.{u}` (module
  `Langlands.BaseChange.CuspFormOrbitalVanishingStatement`): for a nonarchimedean local field
  `F : Type u` of characteristic zero, `0 < n`, every Haar measure `μF` on `GL_n(F)` and every
  Schwartz–Bruhat `f` with `HasVanishingConstantTerms f`, `OrbitalIntegralsVanishOffElliptic μF f`
  (the orbital integrals of `f` vanish at the regular semisimple elements that are not regular
  elliptic).
- `SupercuspidalEllipticPseudoCoefficientStatement.{u, uV, uW}` (module
  `Langlands.BaseChange.SupercuspidalEllipticPseudoCoefficientStatement`): for the same `F`,
  `0 < n`, an irreducible supercuspidal `π` on `V : Type uV` with central character `χ` and a Haar
  measure `μ`, there is a Schwartz–Bruhat `f` with `OrbitalIntegralsVanishOffElliptic μ f`,
  `tr π(f) = 1`, and `tr ρ(f) = 0` for every irreducible admissible `ρ` on `W : Type uW` with
  central character `χ` not isomorphic to `π`.

Both use the same topology and Borel σ-algebra on `GL_n(F)`
(`LocalFieldTopology.generalLinear_t2Space`, `generalLinear_locallyCompactSpace`,
`generalLinear_totallyDisconnectedSpace`, `borel`).

## Proof

After introducing the field, `n`, `0 < n` and the instances on `GL_n(F)` of the statement, the
proof takes `π`, `χ` and `μ` and applies
`SupercuspidalCutoff.exists_cuspForm_pseudoCoefficient` (module
`Langlands.BaseChange.SupercuspidalCutoffPseudoCoefficient`), which gives a Schwartz–Bruhat `f`
with `HasVanishingConstantTerms f`, `tr π(f) = 1` and `tr ρ(f) = 0` for every `ρ` as above. The
hypothesis `CuspFormOrbitalVanishingStatement`, applied to `F`, `n`, `μ` and `f`, turns the
vanishing constant terms into `OrbitalIntegralsVanishOffElliptic μ f`.

The construction of `f` (the cut-off normalized coefficient `c(s)⁻¹ · 1[0 ≤ ord det g < n] ·
ℓ(π(g⁻¹) s)`) and the proofs of its properties are in the modules
`Langlands.BaseChange.PeriodicWindowIntegral`, `Langlands.BaseChange.SupercuspidalCutoffCoefficient`,
`Langlands.BaseChange.SupercuspidalCutoffTraces` and
`Langlands.BaseChange.SupercuspidalCutoffPseudoCoefficient`; their Markdown files describe them.
The proof uses the axioms `propext`, `Classical.choice` and `Quot.sound` only.

## Provenance

The implication is derived content. It is the division of the proof sketched in the Markdown of
`SupercuspidalEllipticPseudoCoefficientStatement` into its representation-theoretic part
(steps 1–3 and the vanishing of constant terms in step 4) and the descent of orbital integrals of
cusp forms (the rest of step 4), which is `CuspFormOrbitalVanishingStatement`. In the sources,
this descent is the formula of Arthur–Clozel (1989), source ID `arthur-clozel-1989-base-change`,
Chapter 1, proof of Proposition 2.7 (printed p. 16), used in their Lemma 2.12 (ii) (printed
p. 19), and Henniart–Lemaire (2011), II.4.5, formula (1) (printed pp. 86–88), the source of the
Markdown of `CuspFormOrbitalVanishingStatement`.
