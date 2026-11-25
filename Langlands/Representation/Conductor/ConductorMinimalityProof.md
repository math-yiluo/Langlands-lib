# Proof of the conductor lower bound and scaled identity at the conductor level

Module
`Langlands.Representation.Conductor.ConductorMinimalityProof`. It contains one
theorem,

```lean
theorem Langlands.Conductor.conductorMinimalityStatement :
    ConductorMinimalityStatement.{uF, uV}
```

which proves the published
[`ConductorMinimalityStatement`](ConductorMinimalityStatement.md) over every
nonarchimedean local field, with no hypotheses. The axioms are `propext`,
`Classical.choice` and `Quot.sound`.

## Proof

The proof is one application of the published reduction
`Langlands.Conductor.conductorMinimalityStatement_of_sphericalFunctionalEquation`
([`ConductorMinimalityReduction`](ConductorMinimalityReduction.md)) to the
published proofs of its two premises:

- `hFE : SphericalLaurentFunctionalEquationStatement.{uF, uV}` is
  `Langlands.Conductor.sphericalLaurentFunctionalEquation`
  ([`SphericalLaurentFunctionalEquationProof`](SphericalLaurentFunctionalEquationProof.md),
  module `Langlands.Representation.Conductor.SphericalLaurentFunctionalEquationProof`);
- `hinj : Whittaker.MirabolicRestrictionInjectivityStatement.{uF, uV}` is
  `Langlands.Whittaker.mirabolicRestrictionInjectivity`
  ([`MirabolicRestrictionInjectivityProof`](../Whittaker/MirabolicRestrictionInjectivityProof.md),
  module `Langlands.Representation.Whittaker.MirabolicRestrictionInjectivityProof`).

The universes `uF`, `uV` are the same in all three statements. Nothing else is
used. The reduction's Markdown explains how the two premises give both clauses
of the target: the lower bound `v ≠ 0 → m ≤ u` and the scaled identity at
`u = m`.

## Source

H. Jacquet, I. I. Piatetski-Shapiro and J. Shalika, *Conducteur des
représentations du groupe linéaire*, Math. Ann. 256 (1981), 199–214
(registered `jpss-1981-conductor`): the end of the proof of Theorem (5.1),
printed pages 213–214. The statement's Markdown gives the correspondence
between the source and the Lean statement. The reduction's Markdown says where
its Lean argument differs from the source.
