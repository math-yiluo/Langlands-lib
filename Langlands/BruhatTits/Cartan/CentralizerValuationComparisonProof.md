# Real comparison for the actual centralizer of a maximal split torus

Author: Worker 3981 (task `0becf90b-3422-4e36-bbc1-55342700202d`).

```lean
theorem Langlands.BruhatTits.Cartan.centralizerValuationComparison :
    CentralizerValuationComparisonStatement.{u}
```

This proves the statement in
[`CentralizerValuationStatement`](CentralizerValuationStatement.md), at an
arbitrary universe `u`. Let `F` be a nonarchimedean local field, of either
characteristic, and let `G` be a connected reductive group scheme over `Spec F`.
No split, quasi-split or tame condition is imposed on `G`. Let `i : S ⟶ G` be a
maximal split torus. Let `j : Z ⟶ G` be a closed subgroup representing the
all-test-scheme centralizer `torusCentralizer i`, and let `s : S ⟶ Z` satisfy
`s ≫ j = i`. Then `restrictionEvaluation s : V(S) → Hom(X^*(Z), ℝ)` is bijective.
Here `V(S)` is the real cocharacter space and `X^*(Z)` is `rationalCharacters Z`.

## Declarations

- `characterRestrict_injective_finiteIndex_of_torusCentralizer hG hi hj hZ hs`.
  Over every field, with the same data as above, actual restriction
  `characterRestrict s : X^*(Z) → X^*(S)` is injective and its range has finite
  index.
- `restrictionEvaluation_bijective_of_torusCentralizer hG hi hj hZ hs`. Over
  every field, with the same data, `restrictionEvaluation s` is bijective.
- `centralizerValuationComparison`. The target, obtained by applying the
  previous theorem to the given nonarchimedean local field. The local-field
  hypotheses are not used.

## Proof

All the structural inputs are proved Library theorems; none is a hypothesis.

1. *Structure of `Z`.* The published
   `Langlands.BruhatTits.Cartan.actualCentralizerStructure`, the proof of
   `ActualCentralizerStructureStatement`, applies to the same data
   `G, S, i, Z, j, s`. It gives that `Z` is connected reductive and that `s` is
   a split component of `Z` (`IsSplitComponent s`).
2. *Finite index.* The published
   `IsSplitComponent.finiteIndex_range_characterRestrict` (module
   `Langlands.GroupScheme.Rational.CharacterRestrictionFiniteIndex`) shows that
   restriction of rational characters to a split component of a connected
   reductive group has finite-index range. It is applied to `Z` and `s`.
3. *Injectivity.* The published
   `characterRestrict_injective_of_centralSplitTorusCharacter` (module
   `Langlands.GroupScheme.Rational.CharacterRestrictionInjective`) derives
   injectivity of restriction to a split component from
   `CentralSplitTorusCharacterStatement`. That statement says that every nonzero
   rational character of a connected reductive group is nonzero on some central
   split torus. Its proof `Langlands.GroupScheme.centralSplitTorusCharacter`
   (module `Langlands.GroupScheme.Rational.CentralSplitTorusCharacterProof`) is
   supplied as the argument. The result is applied to `Z` and `s`.
4. *Real comparison.* The published `restrictionEvaluation_bijective` (module
   `Langlands.BruhatTits.Cartan.CentralizerRealComparison`) shows the following:
   if `S` is an actual split torus and `characterRestrict s` is injective with
   finite-index range, then `restrictionEvaluation s` is bijective. Its proof
   uses the perfect pairing of actual split tori,
   `RealTorusSpace.isPerfPair_of_isSplitTorus`. It then composes with
   `Global.AdelicGroupPoints.realCharacterDualRestrictionEquiv`, the published
   real-dual equivalence for injective finite-index restriction. The split-torus
   hypothesis is the first component of `IsMaximalSplitTorus i`, namely
   `hi.1.1 : IsSplitTorus S.toGrp`. Steps 2 and 3 supply the other two inputs.

## Provenance

The comparison is a derived real-coefficient form of Kaletha–Prasad, *Bruhat–Tits
Theory: A New Approach* (2023), §2.6(d), printed p.103/PDF134. There, restriction
of rational characters to the maximal central split torus is injective with
finite-index image, so the rational dual of the characters is identified with the
rational cocharacters of that torus. Section 5.2, printed p.187/PDF218, applies
this to `Z = Z_G(S)` and the same `S`. The corrections of 1 November 2024
(PDF24–25 and 30) fix the positive normalization `χ(ω_Z(z)) = ord_F(χ(z))` of the
valuation that the comparison enables. That valuation is
`centralizerValuation s h`, which takes this bijectivity as `h`. The present
proof follows this route with `ℝ` coefficients, using the Library's structure,
finite-index, injectivity and split-torus duality theorems listed above.

## Scope

The theorem compares real spaces only. It does not identify the actual valuation
image `centralizerValuationImage` with the integral cocharacter lattice. It gives
no rank, index, representative-set, `Z(F)^0`/`Z(F)^1` or Cartan-quotient
conclusion. It also does not construct a representing centralizer `Z` or the
factorization `s`; these are part of the hypotheses of the target.
