# KP Corollary 11.7.5: rational surjectivity and the chamber quotient, proof

Lean module: `Langlands.Geometry.Building.Kottwitz.ChamberProof`,
namespace `Langlands.Geometry.Building.Kottwitz`.

## Statement

```
theorem Langlands.Geometry.Building.Kottwitz.chamber : ChamberStatement.{u}
```

The type is exactly the published proposition
`Langlands.Geometry.Building.Kottwitz.ChamberStatement.{u}` of the module
`Langlands.Geometry.Building.Kottwitz.ChamberStatement`, at an arbitrary
universe `u`, with no further hypothesis. Unfolded, it reads (with `K` the
maximal unramified extension `inertiaFixedField F`):

```
∀ (F : Type u) [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  (G : GroupScheme (Spec (CommRingCat.of F))) (hG : IsConnectedReductive G),
  Function.Surjective (reductiveKottwitzRational F G hG) ∧
  ∀ (T : CommGroupScheme (Spec (CommRingCat.of F))) (iT : T.toGrp ⟶ G),
    letI : IsAffineHom G.X.hom := hG.isAffineHom
    ∀ (hiT : IsMaximalSplitTorus
        (T := (CommGroupScheme.baseChange (algebraBaseMap F (inertiaFixedField F))).obj T)
        ((GroupScheme.baseChange (algebraBaseMap F (inertiaFixedField F))).map iT)),
      haveI := mono_of_isMaximalSplitTorus hiT
      haveI : Mono ((GroupScheme.baseChange
          (algebraBaseMap F (inertiaFixedField F))).map iT).hom.hom.left :=
        mono_of_isMaximalSplitTorus hiT
      ∀ (D : KPApartmentData
          (S := (CommGroupScheme.baseChange (algebraBaseMap F (inertiaFixedField F))).obj T)
          ((GroupScheme.baseChange (algebraBaseMap F (inertiaFixedField F))).map iT)
          (IntegerValuation.order (MaximalUnramified.valuation F)))
        (C : CentralizerDatum
          (S := (CommGroupScheme.baseChange (algebraBaseMap F (inertiaFixedField F))).obj T)
          ((GroupScheme.baseChange (algebraBaseMap F (inertiaFixedField F))).map iT))
        (h6 : IntegerValuation.IsOmegaCompatible (MaximalUnramified.valuation F) D C)
        (hD : KPApartmentData.GaloisStable F (inertiaFixedField F) iT D),
        let B := UnramifiedBuildingDescent.buildingData iT
          (connectedReductiveFieldExtensionStatement F (inertiaFixedField F) G hG)
          hiT D C h6
        ∀ (Cch : Set B.ReducedBuilding), B.IsChamber Cch →
          (∀ σ : inertiaFixedField F ≃ₐ[F] inertiaFixedField F,
            (UnramifiedBuildingDescent.semilinearData iT
              (connectedReductiveFieldExtensionStatement F (inertiaFixedField F) G hG)
              hiT C h6 hD).action σ '' Cch = Cch) →
          ∀ (S : CommGroupScheme (Spec (CommRingCat.of F)))
            (Z : GroupScheme (Spec (CommRingCat.of F)))
            (i : S.toGrp ⟶ G) (j : Z ⟶ G) (d : ZeroSubgroupDatum i j),
            let P := (MulAction.stabilizer
              (rationalPoints (baseChanged F (inertiaFixedField F) G)) Cch).comap
                (rationalExtend F (inertiaFixedField F) G)
            let N := d.zeroSubgroup.subgroupOf P
            ∃ hN : N.Normal,
              letI := hN
              ∃ e : (P ⧸ N) ≃* Multiplicative (ReductiveInvariantTarget F G hG),
                ∀ x : P, e (QuotientGroup.mk' N x) =
                  reductiveKottwitzRational F G hG x.val
```

In words, with `Γ = Gal(K/F)`, `I` the inertia group and `A = π₁(G)_I`: the
rational Kottwitz homomorphism `κ_G : G(F) → A^Γ` is
surjective; and for supplied Galois-stable building data over `K` and every
Galois-stable chamber `C` of its building, with `P = G(F)_C` the stabilizer of
`C` in `G(F)` and `N = G(F)_C ∩ G(F)^0`, the subgroup `N` is normal in `P` and
`κ_G` induces an isomorphism `P/N ≃ A^Γ`.

## Proof

The Lean proof is the single application

```
chamberStatement_of_remainingInputs specialTorusExistence unramifiedTwistedChamber
  Langlands.BruhatTits.IntegralModels.unramifiedParahoricModel
  Langlands.GroupScheme.IntegralModel.unramifiedSmoothModelDescent
  unramifiedChamberExactSequence reductiveKottwitzDescent_assembled zeroKernel
```

of `chamberStatement_of_remainingInputs` (module
`Geometry.Building.Kottwitz.RationalSurjectivityReduction`), which derives the
statement from seven hypotheses. Each is discharged by a theorem proved in the
Library without hypotheses:

1. `specialTorusExistence` (module `Geometry.Building.SpecialTorusExistenceProof`):
   KP Proposition 9.3.4, special tori exist.
2. `unramifiedTwistedChamber` (module
   `Geometry.Building.UnramifiedTwistedChamberProof`): for every crossed
   homomorphism `Γ → G(K)` trivial on an open subgroup, some chamber is stable
   under the twisted action (KP Proposition 9.10.4).
3. `Langlands.BruhatTits.IntegralModels.unramifiedParahoricModel` (module
   `BruhatTits.IntegralModels.UnramifiedParahoricModelProof`): KP Theorems
   8.3.2 and 8.3.13 over `K`, smooth affine models for bounded subsets.
4. `Langlands.GroupScheme.IntegralModel.unramifiedSmoothModelDescent` (module
   `GroupScheme.IntegralModel.UnramifiedSmoothDescentProof`): KP Fact 2.10.16,
   descent of smooth integral models from the integers of `K`.
5. `unramifiedChamberExactSequence` (module
   `Geometry.Building.Kottwitz.UnramifiedChamberExactSequenceProof`): KP
   Proposition 11.6.1 for the building over `K`.
6. `reductiveKottwitzDescent_assembled` (module
   `Geometry.Building.Kottwitz.ZExtensionKernelProof`): KP Lemma 11.5.1,
   descent of the Kottwitz map to rational points.
7. `zeroKernel` (module `Geometry.Building.Kottwitz.ZeroKernelProof`): KP
   Proposition 11.5.4, `G(F)^0 = ker κ_G`.

Inside the reduction, the first six give the surjectivity of `κ_G`
(`rationalSurjectivityReduction`), and with the seventh the chamber quotient
(`chamberStatement_of_surjective_of_geometricInputs`); the details are on the
page of `Geometry.Building.Kottwitz.RationalSurjectivityReduction`. The
statement is not modified and no hypothesis is added.

## Declarations

- `Langlands.Geometry.Building.Kottwitz.chamber : ChamberStatement.{u}`.

## Literature

T. Kaletha and G. Prasad, *Bruhat–Tits Theory: A New Approach* (2023),
Chapter 11, §11.7, Corollary 11.7.5, printed p. 434: the Kottwitz
homomorphism `κ : G(k) → π₁(G)_I^{Gal(K/k)}` is surjective and induces an
isomorphism `G(k)_C / G(k)^0_C → π₁(G)_I^{Gal(K/k)}`. The formulation of the
chamber clause on supplied building data is described on the statement's
page.
