# Proof of closed common-Levi coherence

Module `Langlands.Representation.Plancherel.ActualCommonLeviCoherenceProof`.
It proves the published proposition
`Langlands.Plancherel.ActualCommonLeviCoherence.ClosedCommonLeviCoherenceStatement`
from `Langlands/Representation/Plancherel/ActualCommonLeviCoherenceStatement.lean`.
The theorem is

```
theorem closedCommonLeviCoherence :
    ClosedCommonLeviCoherenceStatement χ hG A C hC qMeasure hsq hi K hK
```

with the same section variables as the statement: the cocharacter `χ`,
connected reductivity `hG`, the smooth representation `A` of the literal
Levi at independent universes `u` and `uV`, the normal central subgroup `C`
with `hC`, the Haar and inversion-invariant quotient measure `qMeasure`,
square integrability `hsq`, irreducibility `hi`, and the compact open
subgroup `K` with `hK`. There are no further hypotheses. The split-center
premise `IsActualSplitCenter χ C` is part of the proposition itself, as in
the statement.

## Proof

The proof is one application of
`closedCommonLeviCoherence_of_v31` from
`ActualCommonLeviCoherenceAssembly`. That theorem derives the target from
`ClosedV31Statement` for every ordered pair `P Q` of structural parabolic
presentations. Each pair is supplied by the published Library theorem
`Langlands.Plancherel.ActualCommonLeviV3.closedV31` (module
`ActualCommonLeviV3Proof`), applied to the cocharacter, centralizer
equality and Iwasawa decomposition of `P` and of `Q`:

```
closedV31 χ hG A C hC qMeasure hsq hi K hK
  P.cocharacter P.centralizer_eq P.iwasawa
  Q.cocharacter Q.centralizer_eq Q.iwasawa
```

The argument behind `closedCommonLeviCoherence_of_v31` is in two modules:

- `ActualCommonLeviCoherenceAssembly` takes the published proof
  `ActualCommonLeviV3.denseUnitaryIrreducibility` (unitary parameters with
  irreducible actual normalized induction are dense) and the published
  `ActualCommonLeviV3.coefficientMap_injective_of_isIrreducible`
  (irreducibility makes the actual coefficient map injective). Together
  they show that, for every presentation `P`, the unitary parameters where
  the coefficient map of `P` is injective form a dense set.
- `ActualCommonLeviCoherenceReduction` proves
  `closedCommonLeviCoherence_of_v31_of_dense_injective`. Given V.3.1 for
  all pairs, choose a comparison for each ordered pair to get existence.
  A coefficient-preserving bijective comparison is unique at points where
  the source coefficient map is injective. The same holds for identity and
  composition there. The regular unitary extension of V.3.1 makes the
  fixed compact-carrier values of each comparison locally finite, so they
  are weakly continuous. Weakly continuous families that agree on a dense
  set agree everywhere. This gives presentation independence and the
  identity and composition laws at every unitary parameter. The inverse law
  follows from the published `inverseLaw_of_identity_composition`.

## Provenance

The target specializes Waldspurger, *La formule de Plancherel pour les
groupes p-adiques* (2003), Lemmas V.3.1 and V.3.2 with `s = t = 1`, printed
p.295 / PDF p.61 (source `waldspurger-2003-plancherel`). Waldspurger derives
V.3.2 from the composition rule IV.1(12) of standard intertwining
operators. This formal proof does not take that route. It combines the
coefficient identity of V.3.1 with density of irreducible unitary points
(Waldspurger IV.2.2(i), printed p.284) and continuity of the regular
representatives.
