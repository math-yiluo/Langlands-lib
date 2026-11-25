# The action of `N(F) ∩ G(F)^♮` on the apartment has image `W(Ψ)`: proof

Lean module: `Langlands.Geometry.Building.SimplyConnectedNormalizerAffineWeylProof`,
namespace `Langlands.Geometry.Building`.

## Statement

```
theorem Langlands.Geometry.Building.simplyConnectedNormalizerAffineWeyl :
    SimplyConnectedNormalizerAffineWeylStatement.{u}
```

The type is exactly the published proposition
`Langlands.Geometry.Building.SimplyConnectedNormalizerAffineWeylStatement.{u}`
of the module
`Langlands.Geometry.Building.SimplyConnectedNormalizerAffineWeylStatement`, at
an arbitrary universe `u`, with no further hypothesis. Unfolded, it reads:

```
∀ (F : Type u) [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F] (G : GroupScheme (Spec (CommRingCat.of F)))
  [IsAffineHom G.X.hom] (P : ParahoricBuildingData G),
  P.apartment.SatisfiesApartmentAxioms P.centralizer →
    (P.simplyConnectedImage.subgroupOf (normalizerPoints P.i)).map
        P.apartment.normalizerAffineEquiv =
      AffineRootSystem.affineWeylGroup P.affineRoots
```

In words: for every nonarchimedean local field `F`, every affine group `G`
over `F` and parahoric building data `P` whose apartment satisfies the
apartment axioms, the image of `N(F) ∩ G(F)^♮`, where `G(F)^♮` is the image of
the rational points of the simply connected cover, under the action on the
apartment is exactly the affine Weyl group `W(Ψ)` of the affine roots.

The Library also contains the theorem
`Langlands.Geometry.Building.MaximalUnramified.simplyConnectedNormalizerAffineWeyl`
(module `Geometry.Building.UnramifiedSimplyConnectedNormalizerAffineWeylProof`),
a different statement in the namespace `MaximalUnramified`.

## Proof

The Lean proof is the single application

```
simplyConnectedNormalizerAffineWeyl_of_affineIwahoriTits affineIwahoriTits
```

of the theorem `simplyConnectedNormalizerAffineWeyl_of_affineIwahoriTits`
(module `Geometry.Building.AffineIwahoriTitsNormalizerReduction`) to
`affineIwahoriTits : AffineIwahoriTitsStatement.{u}` (module
`Geometry.Building.AffineIwahoriTitsProof`), proved without hypotheses.

Inside the reduction, the inclusion `W(Ψ) ⊆` image is the rank-one
realization of the affine reflections by elements of `N(F) ∩ G(F)^♮`; the
inclusion image `⊆ W(Ψ)` applies the Iwahori–Tits system of one chamber,
whose action-compatible equivalence `P.affinePart ≃* W(Ψ)` places the action
of every element of `N(F) ∩ G(F)^0`, hence of `N(F) ∩ G(F)^♮`, in `W(Ψ)`. The
details are on the page of
`Geometry.Building.AffineIwahoriTitsNormalizerReduction`. The statement is not
modified and no hypothesis is added.

## Declarations

- `Langlands.Geometry.Building.simplyConnectedNormalizerAffineWeyl :
  SimplyConnectedNormalizerAffineWeylStatement.{u}`.

## Literature

T. Kaletha and G. Prasad, *Bruhat–Tits Theory: A New Approach* (2023),
Chapter 7, §7.5, Theorem 7.5.3(2), printed p. 261: the action of `N_G(T)(k)`
on the apartment identifies the Weyl groups of the Tits systems `(G, I, N, R)`
and `(G^♮, I^♮, N^♮, R)` with the Weyl group of `Ψ`; the Lean statement is the
image part for `N^♮ = N(F) ∩ G(F)^♮`. Theorem 7.5.1 is on printed pp. 259–260
and Lemma 7.5.2 on printed p. 260. The authors' *Corrections and additions*
(version of 1 November 2024), p. 33, add AS 5 to the opening assumptions of
Chapter 7.
