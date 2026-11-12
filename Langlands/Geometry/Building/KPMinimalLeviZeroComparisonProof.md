# KP Lemma 2.6.27 and Corollary 2.6.28 for the actual minimal-Levi zero subgroup

Worker 4631. The theorem
`Langlands.Geometry.Building.ZeroSubgroupDatum.minimalLeviZeroComparison`
proves exactly
`Langlands.Geometry.Building.ZeroSubgroupDatum.MinimalLeviZeroComparisonStatement`
from `Langlands.Geometry.Building.KPMinimalLeviZeroStatement`. It holds for
every actual `E : ZeroSubgroupDatum i j` over every nonarchimedean local
field `F`, of either characteristic, at arbitrary universe `u`. The variables
and binders are those of the statement module. The theorem adds no premise.

The statement is the conjunction of two assertions:

```text
IsSimplyConnected G → E.centralizerZero = Plancherel.rationalCommonNormKernel Z
E.zeroSubgroup.comap (rationalPoints.map j) ⊓
  Plancherel.rationalCommonNormKernel Z = E.centralizerZero
```

The first is `Z(F)^0 = Z(F)^1` for a simply connected ambient group (KP
Lemma 2.6.27, over `F`). The second is `G(F)^0 ∩ Z(F)^1 = Z(F)^0` (KP
Corollary 2.6.28). Both use the published `centralizerZero` and
`zeroSubgroup` of the supplied datum `E`; neither is replaced.

## Proof

The proof is a single application of the published conditional assembly
`ZeroSubgroupDatum.minimalLeviZeroComparison_of_inputs`, from
`Langlands.Geometry.Building.KPCoverImageReduction`. That assembly
proves the target for every `E` from six universe-`u` structural
propositions. Its first conjunct comes from
`centralizerZeroNormKernel_of_inputs` in
`Langlands.Geometry.Building.KPMinimalLeviZeroNormKernelReduction`, and its
second from `centralizerZeroIntersection_of_inputs`. The Markdown files of
those two modules describe how the actual zero subgroups and the choices in
`E` are compared. This module supplies each of the six propositions from a
published Library proof. Item 1 is an auxiliary proposition `hspan`, which
items 2–4 use; items 2–6 are the six inputs.

1. `hspan : SplitSimplyConnectedCorootSpanStatement.{u}`
   (`Langlands.GroupScheme.SimplyConnected.SplitNecessityStatement`):
   coroots of a split simply connected group span its cocharacter lattice
   (necessity in Milne, Proposition 23.59). It is
   `splitSimplyConnectedCorootSpan_of_inputs` applied to the triple
   `splitReductiveExistence`, `splitCentralIsogenyExistence`,
   `splitSemisimpleRootDatum`.
2. `hsc : IsSimplyConnectedFieldExtensionStatement.{u}`
   (`Langlands.GroupScheme.SimplyConnected.FieldExtensionStatement`):
   simple connectedness is preserved by every field extension. It is
   `isSimplyConnectedFieldExtension_of_descent_and_splitStructure` applied to
   `simplyConnectedCoverTensorDescent`, `splitSimplyConnectedCoverExistence`,
   `simplyConnectedCentralCoverUniversalProperty`, `maximalTorusBaseChange`,
   `rootDatumExistence`, `hspan` and `splitCorootSpanSimplyConnected`.
3. `hF : SplitTorusCentralizerCocenterInducedStatement.{u}`
   (`Langlands.GroupScheme.Rational.SplitTorusCentralizerCocenterStatement`):
   the cocenter of a split-torus centralizer in a simply connected group is an
   induced torus. It is `splitTorusCentralizerCocenterInduced_of_inputs`
   applied to the tuple `dynamicCentralizerReductive`,
   `cocenterQuotientExistence`, `hsc`, `hspan` and
   `splitTorusCentralizerCocenterRootModel`.
4. `hG : SplitTorusCentralizerDerivedSimplyConnectedStatement.{u}`
   (`Langlands.GroupScheme.SimplyConnected.SplitTorusCentralizerDerivedStatement`):
   the derived subgroup of such a centralizer is simply connected. It is
   `splitTorusCentralizerDerivedSimplyConnected_of_inputs` applied to
   `dynamicCentralizerReductive`, to
   `derivedSubgroupSemisimple_of_rootDatum_product rootDatumExistence
   derivedMaximalTorusProductSurjectivity`, to `hspan`,
   `splitCorootSpanSimplyConnected` and
   `splitTorusCentralizerDerivedCorootComparison`. Its last argument is the
   algebraic-closure ascent
   `isSimplyConnectedAlgebraicClosureAscent_of_descent_and_splitStructure`,
   with the same seven arguments as in item 2.
5. `hPL : SplitTorusCentralizerCoverPreimageStatement.{u}`
   (`Langlands.GroupScheme.SimplyConnected.SplitTorusCentralizerCoverPreimageStatement`):
   the preimage of a split-torus centralizer in a simply connected central
   cover. It is `splitTorusCentralizerCoverPreimage_of_inputs` applied to
   `reductiveCentralDerivedProduct`, `dynamicCentralizerReductive` and `hG`.
6. `cocenterQuotientExistence`
   (`CocenterQuotientExistenceStatement.{u}`, from
   `Langlands.GroupScheme.Derived.CocenterQuotientStatement`) and
   `inducedTorusIwahori`
   (`InducedTorusIwahoriStatement.{u}`, KP Lemma 2.5.18 over `K`, from
   `Langlands.Geometry.Building.KPInducedTorusIwahoriStatement`) are used
   directly.

The final step is

```text
E.minimalLeviZeroComparison_of_inputs cocenterQuotientExistence hF hG
  inducedTorusIwahori hPL hsc
```

Declarations ending in `_of_inputs`, `_of_descent_and_splitStructure` or
`_of_rootDatum_product` are published conditional assemblies, and every one
of their hypotheses is supplied above. Each remaining cited declaration is a
published theorem whose type is exactly its statement, with no hypotheses,
used at universe `u` (`simplyConnectedCoverTensorDescent` at `.{u, u}`); the
Lean imports name their modules. Every argument is therefore
a closed term, and the composite proof has no premise. The development check
reports only the axioms `propext`, `Classical.choice` and `Quot.sound`.

## Provenance

This is an internal assembly. The mathematical route is that of
Kaletha–Prasad, *Bruhat–Tits Theory: A New Approach* (2023), registered as
`kaletha-prasad-2023-bruhat-tits-new-approach`: Lemma 2.6.27 and
Corollary 2.6.28, printed pages 105–106 / PDF pages 136–137. The published
conditional assemblies carry that route and their Markdown cites it. This
module adds only the instantiation of their hypotheses with published proofs.
The Milne citation in item 1 repeats the description in the
docstring of `splitSimplyConnectedCorootSpan_of_inputs`.
