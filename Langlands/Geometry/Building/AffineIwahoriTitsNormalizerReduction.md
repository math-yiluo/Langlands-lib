# The apartment-only affine Iwahori–Tits statement is equivalent to KP Theorem 7.5.3(2), range part

`AffineIwahoriTitsNormalizerAffineWeylEquivalenceStatement.{u}` is the Prop-valued `def`

```text
AffineIwahoriTitsStatement.{u} ↔ SimplyConnectedNormalizerAffineWeylStatement.{u}
```

Both sides are unchanged published targets:

- `AffineIwahoriTitsStatement` is the `G(F)^0` branch of Kaletha–Prasad Theorem 7.5.3(1),(2)
  for actual building data under the apartment axioms. For every chamber `C` it gives both
  normalities and an affine Tits system for the generated parahoric, the restricted normalizer,
  the `affinePart` quotient and the geometric chamber-simple reflections. The Tits system comes
  with an action-compatible equivalence `e : P.affinePart ≃* W(Ψ)` and the saturation formula.
- `SimplyConnectedNormalizerAffineWeylStatement` is the range part of KP Theorem 7.5.3(2): the
  image of `N(F) ∩ G(F)^♮` in the affine automorphisms of the apartment is exactly `W(Ψ)`.

`affineIwahoriTitsStatement_iff_simplyConnectedNormalizerAffineWeyl` proves the equivalence.
Neither side is proved here. The module shows that, given the Library's proved inputs, the
apartment-only Iwahori–Tits target is exactly as hard as the range statement. The module also
records reductions of the target to the open statements below the range statement in the
published route.

## Forward direction

`affineIwahoriTitsStatement_of_simplyConnectedNormalizerAffineWeyl hW` is a composition of
published theorems:

1. `iwahoriWeylNormalizerAffineWeylReduction hW` gives `IwahoriWeylExactSequenceStatement`, which
   is KP Theorem 7.8.1(1) with both normalities and the action-compatible equivalence
   `P.affinePart ≃* W(Ψ)`. Its first component is used.
2. `affineIwahoriTitsStatement_of_inputStatements` (module `AffineIwahoriTitsInputStatements`)
   derives `AffineIwahoriTitsStatement` from the exact sequence and six inputs. All six are
   published proofs: `chamberParahoricNormalizer`, `chamberParahoricGeneration`,
   `affineRankOneTwoCell`, `chamberSimpleFactorization`, `rootGroupParahoricFiltration` and
   `chamberConjugateIntersection`.

## Converse

`simplyConnectedNormalizerAffineWeyl_of_affineIwahoriTits h` proves the range statement for
given `F`, `G`, `P` and apartment axioms `hA` as follows.

- `⊇`: this is the published
  `affineWeylGroup_le_simplyConnectedNormalizer_map_of_rankOneStatement`, applied to the proved
  rank-one factorization `rootRankOneFactorization`. Every affine reflection is realized by an
  actual normalizer element in the image of the simply connected cover.
- `⊆`: one actual chamber is needed. The actual affine roots of `P` form an affine root system
  (`ValuationBuildingData.isAffineRootSystemWithRankZero_affineRoots`), hence a locally finite
  reflection arrangement. `AffineRootSystem.baseChamber` then chooses a chamber `C`, without any
  positive-rank assumption. Applying `h` to `C` gives `e` and `he : P.AffineIwahoriTitsWith C e`.
  Let `n ∈ N(F)` lie in `G(F)^♮ = P.simplyConnectedImage`. Then `n ∈ G(F)^0` by
  `ZeroSubgroupDatum.simplyConnectedImage_le_zeroSubgroup`, since `G(F)^0` is defined as
  `G(F)^♮ ⊔ Z(F)^0`. So `n` defines an element of `P.normalizerZeroComponent`. The field
  `he.action_compatible` rewrites its apartment action `P.apartment.normalizerAffineEquiv n` as
  `e (P.affinePartMk n)`, which lies in `W(Ψ)` because `e` takes values in that subgroup.

The converse uses only the action-comparison field of the Iwahori–Tits conclusion. It shows
that this field alone already contains the range statement. So the target has no route that
avoids the range statement.

## Reductions further down the published route

Each of the following theorems has `AffineIwahoriTitsStatement.{u}` as its conclusion, and each
composes published theorems:

- `affineIwahoriTitsStatement_of_simplyConnectedFacetFixing (hfix : SimplyConnectedFacetFixingStatement)`
  uses `simplyConnectedNormalizerAffineWeylReduction hfix derivedCentralSplitTorusProduct`. The
  split-torus product statement is proved.
- `affineIwahoriTitsStatement_of_simplyConnectedKneserTitsCentralizer
  (hKT : SimplyConnectedKneserTitsCentralizerStatement)` uses
  `simplyConnectedFacetFixing_of_kneserTitsCentralizer`.
- `affineIwahoriTitsStatement_of_localKneserTits (hKT : LocalKneserTitsStatement)` uses
  `simplyConnectedKneserTitsCentralizer_of_factors`. Its two other inputs are proved:
  `simplyConnectedAlmostSimpleRationalGeneration` and
  `simplyConnectedAnisotropicFactorCentralizer`. The factor input comes from
  `simplyConnectedKneserTitsFactor_of_localKT_and_structural_inputs`, whose structural inputs
  are also proved: `semisimpleNormalIsogenyComplement`, `rationalBruhat`,
  `rootRankOneFactorization`, `parabolicDynamic` and `smoothMaximalSplitTorusConjugacy`.
- `affineIwahoriTitsStatement_of_localArithmeticInputs` takes the three remaining open local
  arithmetic statements as hypotheses: `LocalSimplyConnectedCocycleVanishingStatement`,
  `LocalRankOneClassificationStatement` and `Quaternionic.LocalSpinKneserTitsStatement`. It
  applies `localKneserTits_of_rankOneLeviFactors_of_classification`; every other input of that
  theorem is a published proof: `rankOneLeviFactorExistence`, `rankOneLeviDerivedGeneration`,
  `rankOneLeviCocenterGeneration`, `simplyConnectedAlmostSimpleWeilRestriction`,
  `affineWeilSplitRank`, `affineWeilParabolicElementarySubgroup` and
  `Quaternionic.localSymplecticKneserTits`.

No hypothesis is added to the building data. Every theorem keeps the arbitrary universe `u`
and the target's only geometric premise, the published apartment-axiom predicate. The open
statements appear only as explicit premises; none is claimed proved.

## Provenance

The provenance is internal: the module composes published Library theorems, and its one new
argument is the short converse above. The contextual source is Kaletha–Prasad, *Bruhat–Tits
Theory: A New Approach* (2023), `kaletha-prasad-2023-bruhat-tits-new-approach`, SHA-256
`05ad9a284a2577b34d1a270228b74dfb28f520561ae7772d8f38dddb78938732`, Theorem 7.5.3 with
Lemma 7.5.2, printed pp. 260–261 (PDF pp. 291–292). In KP's proof of Theorem 7.5.3, the
Tits system `(G^♮, I^♮, N^♮, R)` comes from Theorem 7.5.1 for `G_sc` and the first part of
Lemma 1.4.12. The system `(G, I, N, R)` for `G = G(k)^0` then follows from the second part
of Lemma 1.4.12 and Lemma 7.5.2. So in KP the `G(F)^0` branch rests on the `G(F)^♮` branch,
including its Weyl-group identification. The equivalence here makes this dependence exact
for the Library statements: the `G(F)^0` Tits system holds exactly when
`N(F) ∩ G(F)^♮` acts through `W(Ψ)`. The exact statements of both sides are documented in the
unchanged `AffineIwahoriTitsStatement` and `SimplyConnectedNormalizerAffineWeylStatement`
pairs.
