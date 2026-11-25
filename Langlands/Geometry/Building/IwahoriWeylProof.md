# The Iwahori–Weyl exact sequence and its chamber splitting: proofs

Lean module: `Langlands.Geometry.Building.IwahoriWeylProof`,
namespace `Langlands.Geometry.Building`.

This module proves two of the propositions of
`Langlands.Geometry.Building.IwahoriWeylStatement`: KP Theorem 7.8.1(1) and
KP 7.8.2.

## Statements

```
theorem Langlands.Geometry.Building.iwahoriWeylExactSequence :
    IwahoriWeylExactSequenceStatement.{u}

theorem Langlands.Geometry.Building.iwahoriWeylChamberSplitting :
    IwahoriWeylChamberSplittingStatement.{u}
```

The types are exactly the published propositions, at an arbitrary universe
`u`, with no further hypothesis. Unfolded, they read:

```
IwahoriWeylExactSequenceStatement.{u} =
  ∀ (F : Type u) [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F] (G : GroupScheme (Spec (CommRingCat.of F)))
    [IsAffineHom G.X.hom] (P : ParahoricBuildingData G),
    P.apartment.SatisfiesApartmentAxioms P.centralizer → P.IwahoriWeylExactSequence

IwahoriWeylChamberSplittingStatement.{u} =
  ∀ (F : Type u) [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F] (G : GroupScheme (Spec (CommRingCat.of F)))
    [IsAffineHom G.X.hom] (P : ParahoricBuildingData G),
    P.apartment.SatisfiesApartmentAxioms P.centralizer →
      ∀ C : Set P.Apartment, AffineRootSystem.IsChamber P.affineRoots C →
        P.IwahoriWeylChamberSplitting C
```

where, for fixed data `P`,

```
P.IwahoriWeylExactSequence =
  ∃ (_ : P.normalizerZero.Normal) (_ : P.zeroSubgroup.Normal),
    (∃ e : P.affinePart ≃* AffineRootSystem.affineWeylGroup P.affineRoots,
      ∀ n : P.normalizerZeroComponent,
        (e (P.affinePartMk n) : P.Apartment ≃ᵃ[ℝ] P.Apartment) =
          P.apartment.normalizerAffineEquiv (n : normalizerPoints P.i)) ∧
      P.toComponents.ker = P.affinePart ∧ Function.Surjective P.toComponents

P.IwahoriWeylChamberSplitting C =
  ∃ (_ : P.normalizerZero.Normal) (_ : P.zeroSubgroup.Normal),
    P.affinePart.Normal ∧ P.affinePart.IsComplement' (P.chamberStabilizer C) ∧
      Function.Bijective (P.toComponents.comp (P.chamberStabilizer C).subtype)
```

In words, for parahoric building data `P` of a group `G` over a
nonarchimedean local field whose apartment satisfies the apartment axioms:

- `iwahoriWeylExactSequence`: `Z(F)^0` is normal in `N(F)` and `G(F)^0` is
  normal in `G(F)`; the action on the apartment identifies
  `(N(F) ∩ G(F)^0)/Z(F)^0` with the affine Weyl group `W_aff = W(Ψ)`; and this
  subgroup of the Iwahori–Weyl group `W̃^0 = N(F)/Z(F)^0` is the kernel of the
  surjection `W̃^0 → G(F)/G(F)^0`.
- `iwahoriWeylChamberSplitting`: for every chamber `C` of the apartment, the
  stabilizer `W̃^0_C` of `C` is a complement of the normal subgroup `W_aff`,
  so `W̃^0 = W_aff ⋊ W̃^0_C`, and `W̃^0_C → G(F)/G(F)^0` is bijective.

## Proofs

`iwahoriWeylExactSequence` is the single application

```
iwahoriWeylExactSequenceStatement_of_prerequisites unramifiedZeroPointsIndependence
  Langlands.GroupScheme.simplyConnectedCentralizerProduct simplyConnectedNormalizerAffineWeyl
  (fun _ _ _ _ _ _ _ _ _ _ E => E.centralizerZeroIntersection_of_inputs
    Langlands.GroupScheme.cocenterQuotientExistence
    Langlands.GroupScheme.splitTorusCentralizerCocenterInduced inducedTorusIwahori
    Langlands.GroupScheme.splitTorusCentralizerCoverPreimage
    Langlands.GroupScheme.isSimplyConnectedFieldExtension)
```

of `iwahoriWeylExactSequenceStatement_of_prerequisites` (module
`Geometry.Building.IwahoriWeylExactSequenceReduction`), which derives KP
Theorem 7.8.1(1) from four hypotheses. Each is discharged by theorems proved
in the Library without hypotheses:

1. `unramifiedZeroPointsIndependence` (module
   `Geometry.Building.UnramifiedZeroIndependenceProof`): KP Lemma 2.6.24, the
   independence of `H(K)^♮ · T(K)^0` of the data, over the maximal unramified
   extension.
2. `Langlands.GroupScheme.simplyConnectedCentralizerProduct` (module
   `GroupScheme.Rational.SimplyConnectedCentralizerProductProof`): KP
   Fact 2.6.22 for the minimal Levi subgroup, `G(k) = G(k)^♮ · Z(k)`.
3. `simplyConnectedNormalizerAffineWeyl` (module
   `Geometry.Building.SimplyConnectedNormalizerAffineWeylProof`): KP
   Theorem 7.5.3(2), image part, `N(F) ∩ G(F)^♮` acts through exactly `W(Ψ)`.
4. For every zero datum `E`, the second assertion of KP Corollary 2.6.28,
   `G(F)^0 ∩ Z(F)^1 = Z(F)^0`. The function takes the field, its four
   instances, the implicit `S`, `G`, `Z`, `i`, `j` and the datum `E`, and
   applies `ZeroSubgroupDatum.centralizerZeroIntersection_of_inputs` (module
   `Geometry.Building.KPCoverImageReduction`) to five theorems:
   - `Langlands.GroupScheme.cocenterQuotientExistence` (module
     `GroupScheme.Derived.CocenterQuotientProof`): the cocenter of a connected
     reductive group exists as a torus quotient;
   - `Langlands.GroupScheme.splitTorusCentralizerCocenterInduced` (module
     `GroupScheme.Rational.SplitTorusCentralizerCocenterProof`): the cocenter
     of a split-torus centralizer in a simply connected group is an induced
     torus;
   - `inducedTorusIwahori` (module `Geometry.Building.KPInducedTorusIwahoriProof`):
     KP Lemma 2.5.18, `T(K)^0 = T(K)^1` for an induced torus;
   - `Langlands.GroupScheme.splitTorusCentralizerCoverPreimage` (module
     `GroupScheme.SimplyConnected.SplitTorusCentralizerCoverPreimageProof`):
     the preimage of a split-torus centralizer in the simply connected cover;
   - `Langlands.GroupScheme.isSimplyConnectedFieldExtension` (module
     `GroupScheme.SimplyConnected.SimplyConnectedFieldExtensionProof`): simple
     connectedness is preserved by field extension.

`iwahoriWeylChamberSplitting` is the single application

```
iwahoriWeylChamberSplittingStatement_of_exactSequence iwahoriWeylExactSequence
  affineChamberSimpleTransitivity
```

of `iwahoriWeylChamberSplittingStatement_of_exactSequence` (module
`Geometry.Building.IwahoriWeylExactSequenceReduction`) to the exact sequence
above and to `affineChamberSimpleTransitivity` (module
`Geometry.Building.AffineChamberTransitivity`), the chamber consequence of KP
Lemma 1.3.17: between any two chambers there is exactly one element of the
affine Weyl group.

The routes inside the reductions are described on the page of
`Geometry.Building.IwahoriWeylExactSequenceReduction`. The statements are not
modified and no hypothesis is added.

## Declarations

- `Langlands.Geometry.Building.iwahoriWeylExactSequence :
  IwahoriWeylExactSequenceStatement.{u}`;
- `Langlands.Geometry.Building.iwahoriWeylChamberSplitting :
  IwahoriWeylChamberSplittingStatement.{u}`.

## Literature

T. Kaletha and G. Prasad, *Bruhat–Tits Theory: A New Approach* (2023),
Chapter 7, §7.8: Theorem 7.8.1(1), printed pp. 272–273, the exact sequence
`1 → W_aff → W̃^0 → G(k)/G(k)^0 → 1`, whose kernel the proof identifies with
`W_aff` by Theorem 7.5.3 (printed p. 261); and 7.8.2, printed p. 273: for a
chamber `C`, Lemma 1.3.17 gives `W̃^0 = W_aff ⋊ W̃^0_C`, so the sequence splits
and `W̃^0_C → G(k)/G(k)^0` is an isomorphism. The authors' *Corrections and
additions* (version of 1 November 2024), p. 33, add AS 5 to the opening
assumptions of Chapter 7.
