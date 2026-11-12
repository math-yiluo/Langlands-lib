# The chamber parahoric–normalizer intersection (KP Lemma 7.5.2(1))

This module proves the published statement
`Langlands.Geometry.Building.ChamberParahoricNormalizerStatement` (module
`Langlands.Geometry.Building.AffineIwahoriTitsInputStatements`). The theorem is

```
theorem chamberParahoricNormalizer : ChamberParahoricNormalizerStatement.{u}
```

at an arbitrary universe `u`. The statement and its hypotheses are unchanged. Worker 4681 is
the author.

## What is proved

Let `F : Type u` be a nonarchimedean local field and `G` a group scheme over `Spec F` with
`[IsAffineHom G.X.hom]`. Let `P : ParahoricBuildingData G` satisfy
`P.apartment.SatisfiesApartmentAxioms P.centralizer`, and let `C` be a chamber of the
apartment (`AffineRootSystem.IsChamber P.affineRoots C`). Then every
`n : normalizerPoints P.i` with `(n : rationalPoints G) ∈ P.parahoric C` lies in
`P.normalizerZero`.

In KP's notation: `I ∩ N(F) ⊆ Z(F)^0` for the Iwahori subgroup `I = P_C = Z(F)^0 · G(F)^♯_C`.
Here `N(F)` is the group of `F`-points of the normalizer of the maximal split torus `S`.
`Z(F)^0` is the actual subgroup `P.centralizerZero` of `Z(F)`, viewed inside `N(F)`.
This module proves only this inclusion. The reverse inclusion `Z(F)^0 ⊆ P_C` holds by
definition (`P.map_centralizerZero_le_parahoric`).

## The proof

The proof is a composition of published Library results. It introduces no new mathematical
argument and no hypothesis beyond those of the statement.

### Step 1: the chamber intersection, with its two inputs

The published theorem
`ParahoricBuildingData.zeroNormalizer_eq_map_centralizerZero_of_isChamber`
(module `PointParahoricNormalizer`) states

```
P.zeroNormalizer C = P.centralizerZero.map (rationalPoints.map P.centralizer.j)
```

that is, `N(F) ∩ P_C = Z(F)^0` inside `G(F)`. It needs the apartment axioms, a chamber `C`
and two algebraic inputs:

- `hrank : RelativeRoot.HasRankOneFactorization P.i`, relative-root rank-one factorization
  for the actual maximal split torus;
- `hZ : P.zeroDatum.CoverImageCentralizerNormKernelStatement`, the cover-image containment
  `G(F)^♮ ∩ Z(F)^1 ⊆ Z(F)^0` from the proof of KP Corollary 2.6.28.

The published proof of that theorem runs as follows. First,
`normalizerAffineEquiv_eq_one_of_mem_chamber_parahoric` uses `hrank` and the apartment
axioms to show that `n` acts trivially on the apartment: `n` fixes every point of `C`, and
`C` spans the apartment. Then `normalizerAffineEquiv_eq_one_iff_of_mem_normalizerZeroComponent`
(module `NormalizerApartmentActionKernel`) uses `hZ` and `P_C ⊆ G(F)^0`
(`P.parahoric_le_zeroSubgroup`). It shows that an element of `N(F) ∩ G(F)^0` acting
trivially lies in `Z(F)^0`.

### Step 2: rank-one factorization

`hrank` is the published unconditional theorem
`Langlands.GroupScheme.rootRankOneFactorization : RootRankOneFactorizationStatement.{u}`
(module `Langlands.GroupScheme.Rational.RootRankOneFactorizationProof`). It is applied to
`F`, `G`, `P.isConnectedReductive`, `P.S`, `P.i` and `P.isMaximalSplitTorus`.

### Step 3: the cover-image containment

`hZ` is the published conditional theorem
`ZeroSubgroupDatum.coverImageCentralizerNormKernel_of_inputs` (module
`KPCoverImageReduction`), applied to `P.zeroDatum`. It takes five structural statements,
and each has a published proof or a published reduction to proved inputs:

| Input | Statement | Supplied by |
| --- | --- | --- |
| `hC` | `CocenterQuotientExistenceStatement` | `cocenterQuotientExistence` |
| `hF` | `SplitTorusCentralizerCocenterInducedStatement` | `splitTorusCentralizerCocenterInduced_of_inputs` (see below) |
| `hB1` | `InducedTorusIwahoriStatement` (KP Lemma 2.5.18) | `inducedTorusIwahori` |
| `hPL` | `SplitTorusCentralizerCoverPreimageStatement` | `splitTorusCentralizerCoverPreimage_of_inputs` (see below) |
| `hsc` | `IsSimplyConnectedFieldExtensionStatement` | `isSimplyConnectedFieldExtension` |

The two inputs that have no direct proof theorem are assembled inside the proof, as local
`have` steps. They are not new public declarations:

- `hF`: `splitTorusCentralizerCocenterInduced_of_inputs` takes the conjunction of
  `DynamicCentralizerReductiveStatement` (`dynamicCentralizerReductive`),
  `CocenterQuotientExistenceStatement` (`cocenterQuotientExistence`),
  `IsSimplyConnectedFieldExtensionStatement` (`isSimplyConnectedFieldExtension`),
  `SplitSimplyConnectedCorootSpanStatement` (`splitSimplyConnectedCorootSpan`) and
  `SplitTorusCentralizerCocenterRootModelStatement`
  (`splitTorusCentralizerCocenterRootModel`).
- `hPL`: `splitTorusCentralizerCoverPreimage_of_inputs` takes
  `ReductiveCentralDerivedProductStatement` (`reductiveCentralDerivedProduct`),
  `DynamicCentralizerReductiveStatement` (`dynamicCentralizerReductive`) and
  `SplitTorusCentralizerDerivedSimplyConnectedStatement`. The last one, `hG`, is obtained
  from `splitTorusCentralizerDerivedSimplyConnected_of_inputs`, applied to
  `dynamicCentralizerReductive`, `derivedSubgroupSemisimple`,
  `splitSimplyConnectedCorootSpan`, `splitCorootSpanSimplyConnected`,
  `splitTorusCentralizerDerivedCorootComparison` and an algebraic-closure ascent term. That
  term is `isSimplyConnectedAlgebraicClosureAscent_of_descent_and_splitStructure`, applied to
  `simplyConnectedCoverTensorDescent`, `splitSimplyConnectedCoverExistence`,
  `simplyConnectedCentralCoverUniversalProperty`, `maximalTorusBaseChange`,
  `rootDatumExistence`, `splitSimplyConnectedCorootSpan` and
  `splitCorootSpanSimplyConnected`.

### Step 4: conclusion

`P.mem_normalizerZero_iff` turns the goal `n ∈ P.normalizerZero` into membership of
`(n : rationalPoints G)` in the image of `Z(F)^0` in `G(F)`. Rewriting with the equality of
Step 1, it is enough to show `(n : rationalPoints G) ∈ P.zeroNormalizer C`. That is
`normalizerPoints P.i ⊓ P.parahoric C`, and it holds by `n.property` and the hypothesis on `n`.
These closing lines follow the conditional wiring in this task's carried-over shared draft
(`ChamberParahoricNormalizerAssembly`). That draft kept rank-one factorization and the
cover-image comparison as premises; here both are discharged.

`lean_check` builds the module with no errors or warnings. The theorem depends only on the
axioms `propext`, `Classical.choice` and `Quot.sound`.

## Comparison with the source

KP prove Lemma 7.5.2(1) in one sentence: "The identity `I ∩ N = Z` follows from
Corollary 7.4.9." Corollary 7.4.9 gives `N^♯_x = Z^♯_x` for `x` in a chamber `C`. Since
`P_C = Z(k)^0 · G(k)^♯_C` (Definition 7.4.1(4)) and `G(k)^♯_C = G(k)^♯_x` for `x ∈ C`
(Lemma 7.4.4(1)), this gives
`N ∩ I = Z(k)^0 · Z^♯_x`. The inclusion `Z^♯_x ⊆ Z(k)^0` is then KP Lemma 7.4.3,
`Z(k) ∩ G(k)^0_Ω = Z(k)^0`.

The Lean route uses the same two ingredients in a different form:

- KP's proof of Corollary 7.4.9 uses Lemma 7.4.7, which rests on Proposition 7.3.12 and the
  rank-one Lemma 7.1.5. Here its role is played by the published
  `normalizerAffineEquiv_eq_one_of_mem_chamber_parahoric`. That result shows that `n` acts
  trivially on the apartment. It uses rank-one factorization (KP Proposition 2.11.17) and the
  point-exchange inclusion of the proof of KP Proposition 7.3.12 (module
  `PointSharpExchange`).
- KP's Lemma 7.4.3 is a special case of Lemma 7.3.16. That proof uses
  `G(k)^♯ ⊆ G(k)^♮` to reduce to simply connected `G`, then boundedness (Corollary 7.3.14)
  and `Z(k)^1 = Z(k)^0` (Lemma 2.6.27). Here this role is played by the cover-image
  containment `G(F)^♮ ∩ Z(F)^1 ⊆ Z(F)^0` from the proof of KP Corollary 2.6.28. It enters
  through the published kernel identification
  `normalizerAffineEquiv_eq_one_iff_of_mem_normalizerZeroComponent`, which applies it to
  elements of `N(F) ∩ G(F)^0` that act trivially on the apartment.

The corrections of 1 November 2024 (PDF p. 35) change the proof of Lemma 7.5.2: `Z_sc` is
replaced by `Z′`, and "its preimage in `Z′(k)`" by "the preimage of `I^♯ ∩ Z(k)` in
`Z′(k)`". These corrections concern assertions (2) and (3) of the lemma. They do not affect
the one-line proof of assertion (1). Page 33 of the corrections adds AS 5 to the
Chapter 7 hypotheses, and AS 5 is part of `SatisfiesApartmentAxioms`.

## Sources

- Tasho Kaletha and Gopal Prasad, *Bruhat–Tits Theory: A New Approach*, Cambridge
  University Press, 2023. Registered as `kaletha-prasad-2023-bruhat-tits-new-approach`,
  SHA-256 `05ad9a284a2577b34d1a270228b74dfb28f520561ae7772d8f38dddb78938732`.
  - Lemma 7.5.2 and its proof: printed pp. 260–261 / PDF pp. 291–292.
  - Definition 7.4.1 and Lemma 7.4.3: printed p. 255 / PDF p. 286.
  - Lemma 7.4.4: printed pp. 255–256 / PDF pp. 286–287.
  - Lemma 7.4.7 and Corollary 7.4.9: printed pp. 256–257 / PDF pp. 287–288.
  - Lemma 7.3.16: printed p. 252 / PDF p. 283.
- Tasho Kaletha and Gopal Prasad, *Corrections and additions to Bruhat–Tits Theory: A New
  Approach* (version of 1 November 2024), PDF pp. 33, 35. Registered as
  `kaletha-prasad-2024-corrections`, SHA-256
  `23293f51e58d5ceecb91f834743f68058b98431797d2531142415d013fdf61ed`.
