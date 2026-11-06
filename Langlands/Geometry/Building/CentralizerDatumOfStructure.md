# Actual centralizer data over an arbitrary field from two structural statements

Author: Worker 1045.

This internal module constructs
`Langlands.Geometry.Building.CentralizerDatum.ofStructure` at arbitrary universe
`u`. Let `k : Type u` be any field, `G` a group scheme over
`Spec (CommRingCat.of k)` with `IsConnectedReductive G`, and
`i : S.toGrp ⟶ G` a homomorphism with `IsMaximalSplitTorus i`. Then
`ofStructure` builds all seven fields of `CentralizerDatum i`. It uses two
explicit premises:

- `hDCR : DynamicCentralizerReductiveStatement.{u}`, the universal statement
  that every closed representative of the dynamic centralizer of a cocharacter
  of a connected reductive group is connected reductive;
- `hCST : CentralSplitTorusCharacterStatement.{u}`, the universal statement
  that every nonzero rational character of a connected reductive group stays
  nonzero on some central split subtorus.

Both are existing unproved `Prop`-valued Library definitions, documented in
[`Dynamic.CentralizerReductiveStatement`](../../GroupScheme/Dynamic/CentralizerReductiveStatement.md)
and
[`Rational.CentralSplitTorusCharacterStatement`](../../GroupScheme/Rational/CentralSplitTorusCharacterStatement.md).
This module does not prove either. It needs no local-field, henselian,
quasi-split, perfectness or characteristic hypothesis.
By contrast, the existing `CentralizerDatum.ofValuationComparison` works over a
nonarchimedean local field and takes the universal
`Cartan.CentralizerValuationComparisonStatement` as its premise.

## Declarations

In namespace `Langlands.GroupScheme`, with `k` any field, `G` and `M` group
schemes over `Spec k`, and `T` a commutative group scheme over `Spec k`:

- `IsMaximalSplitTorus.isSplitComponent`: if `i : T.toGrp ⟶ G` is a maximal
  split torus and `IsCentral i`, then `IsSplitComponent i`. Maximality among
  all split subtori implies maximality among central ones.
- `IsMaximalSplitTorus.isSplitComponent_torusCentralizerFactor`: let `i` be a
  maximal split torus, `j : M ⟶ G` a closed subgroup (`IsClosedSubgroup j`)
  representing `torusCentralizer i`, and `hj` that representation. Then the
  canonical factor `torusCentralizerFactor i hj : T.toGrp ⟶ M` is a split
  component of `M`.
- `IsMaximalSplitTorus.characterRestrict_torusCentralizerFactor_injective`:
  given `hDCR`, `hCST` and `IsConnectedReductive G`, restriction of rational
  characters `characterRestrict (torusCentralizerFactor i hj)` from `M` to `T`
  is injective.
- `IsMaximalSplitTorus.finiteIndex_range_characterRestrict_torusCentralizerFactor`:
  given `hDCR` and `IsConnectedReductive G`, the range of that restriction has
  finite index.
- `IsMaximalSplitTorus.restrictionEvaluation_torusCentralizerFactor_bijective`:
  given `hDCR`, `hCST` and `IsConnectedReductive G`,
  `Cartan.restrictionEvaluation (torusCentralizerFactor i hj)` is bijective.

In namespace `Langlands.Geometry.Building.CentralizerDatum`:

- `ofStructure hDCR hCST hG i hi : CentralizerDatum i`, a `def` (data).
- `nonempty_of_structure hDCR hCST hG i hi : Nonempty (CentralizerDatum i)`.

## Construction

1. The published theorem `fieldCentralizerRepresentability` gives a group
   scheme `Z` and a closed subgroup `j : Z ⟶ G` representing the whole-torus
   centralizer `torusCentralizer i` on every test scheme. It needs only that
   the structure morphism of `S` to `Spec k` is affine, which holds because
   `S.toGrp` is a split torus.
2. The published `torusCentralizerFactor i hj` factors `i` through `j`, and
   `torusCentralizerFactor_comp` gives the composite. Classical choice selects
   `Z`, `j` and these data.
3. The factor is a maximal split torus of `Z`
   (`IsMaximalSplitTorus.isMaximalSplitTorus_torusCentralizerFactor`) and is
   central in `Z` (`isCentral_torusCentralizerFactor`). By the first lemma it is
   a split component of `Z`.
4. `IsSplitTorus.isConnectedReductive_centralizer_of_dynamic` derives
   `IsConnectedReductive Z` from `hDCR` and `IsConnectedReductive G`.
5. Injectivity of character restriction is
   `characterRestrict_injective_of_centralSplitTorusCharacter`, applied to
   `hCST`, connected reductivity of `Z` and the split component. Finite index is
   the published proved theorem `IsSplitComponent.finiteIndex_range_characterRestrict`,
   applied to the same data.
6. The published `Cartan.restrictionEvaluation_bijective` turns injectivity and
   finite index into bijectivity of `Cartan.restrictionEvaluation`. Its torus
   hypothesis is that `S.toGrp` is a split torus.

## Provenance and scope

This is a derived construction from existing Library declarations. It has no
independent literature assertion or source citation. The two structural
premises carry their own provenance in their Markdown files: Conrad–Gabber–Prasad
for connected reductivity of torus centralizers, and Renard and Milne for the
radical decomposition behind the character statement.

The module does not prove `hDCR` or `hCST`. It does not prove the universal
valuation comparison or construct any apartment, root valuation or affine Weyl
action. It establishes nothing about quasi-split groups beyond what holds for
every connected reductive group.
