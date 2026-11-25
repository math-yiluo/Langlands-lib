# Axiom 4.1.16 for the building of a valuation of the root datum: proof

Lean module: `Langlands.Geometry.Building.IwahoriDecompositionAxiomProof`,
namespace `Langlands.Geometry.Building`.

## Statement

```
theorem Langlands.Geometry.Building.iwahoriDecompositionAxiom :
    IwahoriDecompositionAxiomStatement.{u}
```

The type is exactly the published proposition
`Langlands.Geometry.Building.IwahoriDecompositionAxiomStatement.{u}` of the
module `Langlands.Geometry.Building.IwahoriDecompositionAxiomStatement`, at an
arbitrary universe `u`, with no further hypothesis. Unfolded, it reads:

```
∀ (F : Type u) [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  (G : GroupScheme (Spec (CommRingCat.of F))) [IsAffineHom G.X.hom]
  (P : ParahoricBuildingData G),
  P.SatisfiesApartmentAxioms → P.HasIwahoriDecomposition
```

In words: for parahoric building data `P` of a group over a nonarchimedean
local field satisfying V 7 and AS 2–AS 5, every chamber `C` of the apartment
and every generic cocharacter `ν` of the maximal split torus, with `I` the
stabilizer in `G(F)^0` of the image of `C` in the building and `U^±` the
unipotent radicals `U(±ν)`: the product map
`(U^+(F) ∩ I) × Z(F)^0 × (U^-(F) ∩ I) → G(F)` is injective with image `I`;
for every non-divisible root `a` there is a smallest affine functional `ψ_a`
with derivative `a` non-negative on `C`; and for every enumeration without
repetition of the positive (respectively negative) non-divisible roots, the
ordered product of the groups `U_{ψ_a}` is injective with image `U^+(F) ∩ I`
(respectively `U^-(F) ∩ I`). These are the fields of
`P.IsIwahoriDecompositionAt C ν`, detailed on the statement's page.

## Proof

The Lean proof is the single application

```
iwahoriDecompositionAxiomReduction simplyConnectedNormalizerAffineWeyl
```

of the theorem `iwahoriDecompositionAxiomReduction` (module
`Geometry.Building.IwahoriDecompositionAxiomReduction`), whose type
`IwahoriDecompositionAxiomReductionStatement.{u}` is the implication
`SimplyConnectedNormalizerAffineWeylStatement.{u} →
IwahoriDecompositionAxiomStatement.{u}`. The premise is discharged by
`simplyConnectedNormalizerAffineWeyl` (module
`Geometry.Building.SimplyConnectedNormalizerAffineWeylProof`), proved without
hypotheses: `N(F) ∩ G(F)^♮` acts on the apartment through exactly `W(Ψ)`.

Inside the reduction, the premise gives the chamber splitting of the
Iwahori–Weyl group (KP 7.8.2), hence that an element of `N(F) ∩ G(F)^0`
mapping a chamber onto itself lies in `Z(F)^0`; with this, the Iwahori subgroup
is the parahoric `P_C`, and the published decompositions of `P_C` give the
five fields. The details are on the page of
`Geometry.Building.IwahoriDecompositionAxiomReduction`. The statement is not
modified and no hypothesis is added.

## Declarations

- `Langlands.Geometry.Building.iwahoriDecompositionAxiom :
  IwahoriDecompositionAxiomStatement.{u}`.

## Literature

T. Kaletha and G. Prasad, *Bruhat–Tits Theory: A New Approach* (2023):

- Chapter 4, §4.1, Axiom 4.1.16 (Iwahori decomposition), printed p. 162: for
  a chamber `C` of the apartment of `S`, `I = G(k)^0_C` and any positive system
  of roots, the product map `(U^+(k) ∩ I) × Z(k)^0 × (U^-(k) ∩ I) → I` is
  bijective, and `U^±(k) ∩ I` are the products of the `U_{ψ_a}` in any order.
- 4.1.28, printed p. 166: for the building of Chapter 7, Axiom 4.1.16 is
  proved in Corollary 7.4.9.

The authors' *Corrections and additions* (version of 1 November 2024), p. 27,
add Axiom 4.1.16 to the list of Definition 4.1.26, and p. 33 adds AS 5 to the
opening assumptions of Chapter 7. The Lean statement assumes V 7 in addition,
as described on the statement's page.
