# Actual dynamic irreducible finite length from supercuspidal finite length

Author: Worker 4094, for the exact VI.6.2 proof task
`02257068-4b1f-4c7d-b849-c85a24606658`.

This module states and proves one implication between two published
propositions. It does not prove either proposition.

## The statement

`Langlands.Aubert.General.DynamicIrreducibleInductionFiniteLengthReductionStatement.{u, uV} : Prop`
is the implication

```lean
RationalPointFamily.RationalSupercuspidalInductionFiniteLengthStatement.{u, max (u + 1) uV} →
  DynamicInductionIrreducibleFiniteLengthStatement.{u, uV}
```

- The premise is the published finite-length part of Renard, Théorème VI.5.4
  (`Aubert/General/RationalSupercuspidalInductionFiniteLengthStatement`). For
  every nonarchimedean local field `k : Type u`, every connected reductive
  group over `k`, every maximal split torus and generic cocharacter, and every
  actual standard index `I`, the published `normalizedInductionFunctor`
  sends every irreducible `IsLeviCuspidal` smooth representation of the
  actual standard Levi `levi i ν I` to a representation of finite length. The
  premise is taken at carrier universe `max (u + 1) uV`, not `uV`.
- The conclusion is the published Renard VI.6.2 Lemma for the actual dynamic
  parabolics (`Aubert/General/IrreducibleInductionFiniteLengthStatement`),
  with its exact binders. For every cocharacter `χ` of a connected reductive
  group over a nonarchimedean local field `F : Type u`, with the canonical
  rational-point topology and the published local compactness,
  nonarchimedean-group and closed-radical hypotheses, the published
  `normalizedInductionFunctor` of `P(χ)(F) = Z(χ)(F) ⋉ U(χ)(F)` sends every
  irreducible smooth complex representation of `Z(χ)(F)` with carrier in
  `Type uV` to a representation of finite length.

The two universe parameters `u` and `uV` stay independent. The premise is
used at the larger carrier universe because the published standard
construction lifts the inducing representation's carrier to
`max (u + 1) uV` before it applies the cuspidal embedding.

Neither the premise nor the conclusion is weakened. The implication adds no
other hypothesis: no characteristic-zero, splitness, admissibility,
finite-dimension, transitivity, geometric-lemma or cuspidal-embedding premise.

## The proof

`dynamicIrreducibleInductionFiniteLengthReduction` proves the statement. Given
the premise `hSuper`, it applies the published conditional reduction
`dynamicInductionIrreducibleFiniteLength_of_standard_inputs` (Worker 1212,
`Aubert/General/DynamicIrreducibleInductionFiniteLength`). That reduction has
five hypotheses. The first is `hSuper`. The other four are structural, and
their published proofs are supplied:

| Hypothesis of the reduction | Published proof |
| --- | --- |
| `StandardCocharacterStatement.{u}` | `Langlands.GroupScheme.standardCocharacter` (`GroupScheme/Rational/StandardCocharacterProof`) |
| `StandardLeviIntersectionStatement.{u}` | `Langlands.GroupScheme.standardLeviIntersection` (`GroupScheme/Rational/StandardLeviIntersectionProof`) |
| `RelativeRootSystemStatement.{u}` | `Langlands.GroupScheme.relativeRootSystem` (`GroupScheme/Rational/RelativeRootSystemProof`) |
| `BruhatTits.DynamicParabolicQuotientCompactStatement.{u}` | `Langlands.BruhatTits.dynamicParabolicQuotientCompact` (`BruhatTits/Parabolic/QuotientCompactProof`) |

The proof term is exactly this application. A development check of the module
reports only the axioms `propext`, `Classical.choice` and `Quot.sound`.

For orientation, the imported reduction works as follows. It chooses a
standard presentation of `χ` and identifies `P(χ)(F)`, `Z(χ)(F)` and
`U(χ)(F)` literally with the actual standard parabolic, Levi and radical of
one index. Inside that Levi, the published cuspidal embedding embeds the
irreducible representation into normalized induction of an irreducible
`IsLeviCuspidal` representation of a smaller standard Levi. The published
actual standard induction-in-stages isomorphism, with the same full-parabolic
Haar normalization, then gives an injective intertwiner from the original
induced representation into a representation that has finite length by
`hSuper`. Finite length descends along this injective map. The imported
module's Markdown describes these steps; this module does not change them.

## Provenance and scope

The statement is internal. It records that, after the four structural proofs
above, the finite-length assertion of Renard VI.5.4 on the standard families
is the only input that the published route to the dynamic VI.6.2 Lemma still
lacks. It makes no new literature assertion.

Renard's own proof of the VI.6.2 Lemma (D. Renard, *Représentations des
groupes réductifs p-adiques*, French version dated 9 July 2026, registered as
`renard-2026-representations-groupes-reductifs-padiques`, SHA256
`7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`, printed
p. 178 / PDF p. 184) has the same shape. It uses Théorème VI.5.4 (printed
p. 173) for the supercuspidal case, the corollary of VI.2.1 (from printed
p. 137) to embed a general irreducible representation, and the exactness of
induction and transitivity VI.1.4 (printed p. 136).

The premise remains unproved here. Its exact proof task is
`59ee1ed5-28d6-4574-bb6e-be514fd6f378`. Once that proposition is proved at
carrier universe `max (u + 1) uV`, applying this theorem to it proves
`DynamicInductionIrreducibleFiniteLengthStatement.{u, uV}`. The published
statement pairs and the imported reduction are unchanged.
