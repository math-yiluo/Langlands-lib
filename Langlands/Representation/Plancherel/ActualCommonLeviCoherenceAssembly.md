# Closed common-Levi coherence: assembly of the density input

Module `Langlands.Representation.Plancherel.ActualCommonLeviCoherenceAssembly`.
It combines four Library results with the reduction module
`ActualCommonLeviCoherenceReduction`:

- `ActualCommonLeviV3.coefficientMap_injective_of_isIrreducible`
  (`ActualCommonLeviCoefficientInjectivity`): at a unitary parameter where
  the actual normalized induction of the unitary twist is irreducible, the
  actual coefficient map `ActualCommonLeviV3.coefficientMap` is injective.
- The published proposition
  `ActualCommonLeviV3.DenseUnitaryIrreducibilityStatement`
  (`ActualCommonLeviUnitaryIrreducibilityStatement`): under its four
  premises, for every cocharacter `ψ` with the same actual dynamic
  centralizer, the irreducibility points are dense in the full unitary
  parameter group.
- `ActualCommonLeviV3.denseUnitaryIrreducibility`
  (`ActualCommonLeviUnitaryIrreducibilityProof`): the published proof of
  `DenseUnitaryIrreducibilityStatement χ A C hC qMeasure`.
- `closedCommonLeviCoherence_of_v31_of_dense_injective` from the reduction
  module.

## Declarations

- `dense_injective_of_denseUnitaryIrreducibility`: assume
  `DenseUnitaryIrreducibilityStatement`, the irreducibility of `A` and
  `IsActualSplitCenter χ C`. Then for every structural parabolic
  presentation `P`, the unitary parameters at which
  `presentationCoefficientMap P z` is injective form a dense set. The
  statement is applied with the connected reductive premise `hG`, the
  square-integrability premise `hsq`, the irreducibility premise `hi`, the
  split-center premise and the cocharacter `P.cocharacter` with its
  centralizer equality. Its dense set lies inside the injectivity set by
  `coefficientMap_injective_of_isIrreducible`, so `Dense.mono` gives the
  claim.
- `closedCommonLeviCoherence_of_v31_of_denseUnitaryIrreducibility`:
  `ClosedCommonLeviCoherenceStatement` follows from `ClosedV31Statement` for
  every ordered pair of presentations and from
  `DenseUnitaryIrreducibilityStatement`. It feeds the previous lemma to
  `closedCommonLeviCoherence_of_v31_of_dense_injective`.
- `closedCommonLeviCoherence_of_v31`: `ClosedCommonLeviCoherenceStatement`
  follows from `ClosedV31Statement` for every ordered pair of presentations
  alone. It applies the previous theorem to the published
  `denseUnitaryIrreducibility χ A C hC qMeasure`.

## Provenance

The module is a derived formal assembly; no declaration here is printed in
the source. The target specializes Waldspurger, *La formule de Plancherel
pour les groupes p-adiques* (2003), Lemmas V.3.1 and V.3.2 (with
`s = t = 1`), printed p.295 / PDF p.61 (source
`waldspurger-2003-plancherel`). The density statement used here comes from
Waldspurger's Proposition IV.2.2(i) and the opening of IV.3, printed
pp.284–285.
