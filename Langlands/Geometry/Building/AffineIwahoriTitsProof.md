# The apartment-only affine Iwahori–Tits statement: proof

Lean module: `Langlands.Geometry.Building.AffineIwahoriTitsProof`,
namespace `Langlands.Geometry.Building`.

## Statement

```
theorem Langlands.Geometry.Building.affineIwahoriTits : AffineIwahoriTitsStatement.{u}
```

The type is exactly the published proposition
`Langlands.Geometry.Building.AffineIwahoriTitsStatement.{u}` of the module
`Langlands.Geometry.Building.AffineIwahoriTitsStatement`, at an arbitrary
universe `u`, with no further hypothesis. Unfolded, it reads:

```
∀ (F : Type u) [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F] (G : GroupScheme (Spec (CommRingCat.of F)))
  [IsAffineHom G.X.hom] (P : ParahoricBuildingData G),
  P.apartment.SatisfiesApartmentAxioms P.centralizer →
    ∀ C : Set P.Apartment, AffineRootSystem.IsChamber P.affineRoots C →
      ∃ (_ : P.normalizerZero.Normal) (_ : P.zeroSubgroup.Normal),
        P.AffineIwahoriTits C
```

In words: for every nonarchimedean local field `F`, every affine group `G`
over `F` and parahoric building data `P` whose apartment satisfies the
apartment axioms, and for every chamber `C` of the apartment, the subgroups
`N(F) ∩ G(F)^0` and `G(F)^0` are normal, and `P.AffineIwahoriTits C` holds:
there is an equivalence of the quotient `P.affinePart` with the affine Weyl
group `W(Ψ)` compatible with the actual action on the apartment, the
parahoric of `C` lies in `G(F)^0`, the restricted groups with the
chamber-simple reflections form a Tits system, and the saturation formula
holds.

## Proof

The Lean proof is the single application

```
affineIwahoriTitsStatement_of_localArithmeticInputs
  Langlands.GroupScheme.localSimplyConnectedCocycleVanishing
  Langlands.GroupScheme.localRankOneClassification
  Langlands.GroupScheme.Quaternionic.localSpinKneserTits
```

of the theorem `affineIwahoriTitsStatement_of_localArithmeticInputs` (module
`Geometry.Building.AffineIwahoriTitsNormalizerReduction`), which derives the
statement from three hypotheses. Each is discharged by a theorem proved in the
Library without hypotheses:

1. `localSimplyConnectedCocycleVanishing :
   LocalSimplyConnectedCocycleVanishingStatement.{u}` (module
   `GroupScheme.SimplyConnected.LocalCocycleVanishingProof`): every cocycle of a
   semisimple simply connected group over a nonarchimedean local field on a
   finite separable field cover is a coboundary.
2. `localRankOneClassification : LocalRankOneClassificationStatement.{u}`
   (module `GroupScheme.SimplyConnected.LocalRankOneClassificationProof`): the
   classification of the absolutely almost-simple simply connected groups of
   split rank one over a nonarchimedean local field.
3. `Quaternionic.localSpinKneserTits :
   Quaternionic.LocalSpinKneserTitsStatement.{u}` (module
   `GroupScheme.Quaternionic.LocalSpinKneserTitsProof`): Kneser–Tits for the
   quaternionic spin groups of Witt index one.

Inside the reduction, these three inputs and the structural theorems of the
Library give local Kneser–Tits, then Kneser–Tits for split-torus centralizers,
pointwise fixing of facets by their normalizer stabilizers for simply
connected groups, the image `W(Ψ)` of `N(F) ∩ G(F)^♮`, the Iwahori–Weyl exact
sequence, and finally the Iwahori–Tits system; the chain is on the page of
`Geometry.Building.AffineIwahoriTitsNormalizerReduction`. The statement is not
modified and no hypothesis is added.

## Declarations

- `Langlands.Geometry.Building.affineIwahoriTits : AffineIwahoriTitsStatement.{u}`.

## Literature

T. Kaletha and G. Prasad, *Bruhat–Tits Theory: A New Approach* (2023),
Chapter 7, §7.5, Theorem 7.5.3(1),(2), printed p. 261: the tuples
`(G, I, N, R)` and `(G^♮, I^♮, N^♮, R)` are saturated Tits systems, and the
action of `N_G(T)(k)` on the apartment identifies their Weyl groups with the
Weyl group of the affine root system `Ψ`; with Theorem 7.5.1, printed
pp. 259–260, and Lemma 7.5.2, printed p. 260. The Lean statement is the
`G(F)^0` branch. The authors' *Corrections and additions* (version of
1 November 2024), pp. 33–35, amend the opening assumptions of Chapter 7
(adding AS 5) and §7.5.
