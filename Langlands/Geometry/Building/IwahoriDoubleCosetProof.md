# Proof of the Iwahori double-coset bijection

Lean module: `Langlands.Geometry.Building.IwahoriDoubleCosetProof`,
namespace `Langlands.Geometry.Building`.

This module proves the published target
`Langlands.Geometry.Building.IwahoriDoubleCosetStatement` of
`Langlands/Geometry/Building/IwahoriWeylStatement.lean`. This is KP Theorem 7.8.1(2), with the
injectivity proof replaced as in the authors' 2024 corrections.

## Statement

```
theorem Langlands.Geometry.Building.iwahoriDoubleCoset :
    IwahoriDoubleCosetStatement.{u}
```

The type is exactly the published proposition, at an arbitrary universe `u`, with no further
hypothesis. Unfolded, it reads:

```
IwahoriDoubleCosetStatement.{u} =
  ∀ (F : Type u) [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F] (G : GroupScheme (Spec (CommRingCat.of F)))
    [IsAffineHom G.X.hom] (P : ParahoricBuildingData G),
    P.apartment.SatisfiesApartmentAxioms P.centralizer →
      ∀ C : Set P.Apartment, AffineRootSystem.IsChamber P.affineRoots C →
        P.IwahoriDoubleCosetBijection C
```

where, for fixed data `P` and a chamber `C`,

```
P.IwahoriDoubleCosetBijection C =
  ∃ e : P.IwahoriWeylGroup ≃
      DoubleCoset.Quotient (P.parahoric C : Set (rationalPoints G)) (P.parahoric C),
    ∀ n : normalizerPoints P.i,
      e (QuotientGroup.mk n) =
        DoubleCoset.mk (P.parahoric C) (P.parahoric C) (n : rationalPoints G)
```

In words: let `P` be parahoric building data of a group `G` over a nonarchimedean local field
`F`, of either characteristic, whose apartment satisfies the apartment axioms (V 6, V 7, AS 2–AS 5,
with the AS 5 of the corrected opening of KP Chapter 7). Then for every chamber `C` there is
an equivalence between the full Iwahori–Weyl group `W̃^0 = N(F)/Z(F)^0` (`P.IwahoriWeylGroup`)
and the double cosets `I\G(F)/I` of the full Iwahori subgroup `I = P.parahoric C`. It sends
the class of every actual normalizer point `n ∈ N(F)` to `I n I`. An equivalence is
injective and surjective. The equivalence keeps all components of `W̃^0` and of `G(F)`: it is
not restricted to `N(F) ∩ G(F)^0` or to `G(F)^0`.

## Proof

The theorem is the single application

```
iwahoriDoubleCosetStatement_of_statements iwahoriWeylChamberSplitting affineIwahoriTits
```

of the published reduction `iwahoriDoubleCosetStatement_of_statements` (module
`Geometry.Building.DoubleCosetStatementReduction`). That reduction derives the target from two
published statements, each discharged here by a theorem proved in the Library:

1. `iwahoriWeylChamberSplitting : IwahoriWeylChamberSplittingStatement.{u}` (module
   `Geometry.Building.IwahoriWeylProof`), KP 7.8.2. Under the apartment axioms, for every
   chamber `C`, `Z(F)^0` is normal in `N(F)` and `G(F)^0` is normal in `G(F)`. Moreover
   `W̃^0 = W_aff ⋊ W̃^0_C`, and the stabilizer `W̃^0_C` of `C` maps bijectively onto
   `G(F)/G(F)^0`.
2. `affineIwahoriTits : AffineIwahoriTitsStatement.{u}` (module
   `Geometry.Building.AffineIwahoriTitsProof`), the `G(F)^0` branch of KP Theorem 7.5.3(1),(2).
   Under the apartment axioms, for every chamber `C`, there is an actual affine Iwahori–Tits
   datum `P.AffineIwahoriTits C`. It contains the containment `P.parahoric C ≤ P.zeroSubgroup`
   of the full Iwahori subgroup in `G(F)^0`, and a `Langlands.Group.IsTitsSystem` for the
   restrictions of `I` and `N(F)` to `G(F)^0`. The Weyl group of this Tits system is the
   affine part `(N(F) ∩ G(F)^0)/Z(F)^0` of `W̃^0`.

For each field, group, data, apartment-axiom proof and chamber, the reduction instantiates both
statements at exactly those premises. It then applies the fixed-data assembly
`ParahoricBuildingData.iwahoriDoubleCosetBijection_of_splitting_of_affineIwahoriTits`. That
assembly takes:

- component surjectivity of the chamber stabilizer, from the splitting
  (`chamberStabilizer_toComponents_surjective_of_splitting`);
- the compatibility `affineTitsProjection_coe` of the restricted and full quotient maps;
- the Tits system and the Iwahori containment.

It passes these to `iwahoriDoubleCosetBijection_of_zeroTits` (module
`Geometry.Building.ParahoricDoubleCosetComponents`). That adapter builds the equivalence
through `iwahoriDoubleCosetEquivOfKernelTits` (module
`Geometry.Building.IwahoriDoubleCosetComponents`) and the component Bruhat construction
`Langlands.Group.TitsSystem.componentDoubleCosetEquiv`. Its application lemma gives the
prescribed value `I n I` on every `n ∈ N(F)`.

Neither the normalities, nor the splitting, nor the Tits system, nor any decomposition or
bijection is a premise of `iwahoriDoubleCoset`. Each is a conclusion of the proved theorems
above, derived from the unchanged apartment and chamber hypotheses.

## The corrected injectivity argument

The printed proof of KP Theorem 7.8.1(2) derives injectivity from the equality
`I ∩ N(k) = Z(k)^0` of Lemma 7.5.2 alone. The authors' corrections of 1 November 2024 (PDF
p. 35) state that this is insufficient and replace it as follows. Take two elements of `W̃^0`
with the same image in `I\G(k)/I`. By 7.8.2 (Lemma 1.3.17), write them uniquely as `w₁ρ₁` and
`w₂ρ₂`, with `wᵢ ∈ W_aff` and `ρᵢ ∈ W̃^0_C`. Since `I ⊂ G(k)^0`, Theorem 7.8.1(1) gives
`ρ₁ = ρ₂`. These elements normalize `I`, so `w₁` and `w₂` have the same image in
`I\G(k)^0/I`. The Bruhat decomposition (Proposition 1.4.5) for the Iwahori–Tits system of
Theorem 7.5.3 then gives `w₁ = w₂`.

The implemented proof follows this corrected route; it does not use the bare equality
`I ∩ N(F) = Z(F)^0`.

- Component surjectivity of `W̃^0_C → G(F)/G(F)^0`, from the chamber splitting, chooses for
  every component a chamber-stabilizer representative.
- Such a representative normalizes the full Iwahori subgroup, by the covariance of the
  generated parahorics under `N(F)` (module `Geometry.Building.IwahoriDoubleCosetComponents`).
- The component Bruhat construction `Langlands.Group.TitsSystem.componentDoubleCosetEquiv`
  works as follows for `n, m ∈ N(F)` with `I n I = I m I`. Since `I ⊆ G(F)^0`, `n` and `m`
  have the same component in `G(F)/G(F)^0`; this is the comparison `ρ₁ = ρ₂`. With one
  normalizing representative `r` of that component, `n r⁻¹` and `m r⁻¹` lie in `G(F)^0` and
  have equal `I`-double cosets there, because conjugation by `r` preserves `I`. Bruhat
  uniqueness of the actual Tits system for `I ∩ G(F)^0` and `N(F) ∩ G(F)^0` gives equal
  images in the affine part, and cancelling `r` gives equal classes in `W̃^0`. A single
  representative of the common component suffices; uniqueness of the decomposition `wρ`
  is not needed.

For surjectivity, the construction removes a normalizing representative of the component of
`g ∈ G(F)` and applies Bruhat existence in `G(F)^0`. It then moves the right `I`-factor past
the representative.

## Scope

The result is conditional on actual `ParahoricBuildingData` whose apartment satisfies the
apartment axioms. It does not construct such data for every group, and it does not prove the
validity conditions of KP Definition 4.1.26.

## Literature

T. Kaletha and G. Prasad, *Bruhat–Tits Theory: A New Approach* (2023), §7.8:
Theorem 7.8.1(2) and 7.8.2, printed pp. 272–273 (PDF pp. 303–304); Theorem 7.5.3, printed
p. 261 (PDF p. 292); Lemma 1.3.17 and Proposition 1.4.5. The authors' *Corrections and
additions* (version of 1 November 2024): p. 33 adds AS 5 to the opening assumptions of
Chapter 7, and p. 35 replaces the injectivity proof of Theorem 7.8.1(2) as quoted above.
