# Apartment-compatible descent of the building from the maximal unramified extension: proof

Lean module: `Langlands.Geometry.Building.UnramifiedApartmentDescentProof`,
namespace `Langlands.Geometry.Building`.

## Statement

```
theorem Langlands.Geometry.Building.unramifiedApartmentDescent :
    UnramifiedApartmentDescentStatement.{u}
```

The type is exactly the published proposition
`Langlands.Geometry.Building.UnramifiedApartmentDescentStatement.{u}` of the
module `Langlands.Geometry.Building.UnramifiedApartmentDescentStatement`, at an
arbitrary universe `u`, with no further hypothesis. Unfolded, it reads:

```
∀ (F : Type u) [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  (G : GroupScheme (Spec (CommRingCat.of F))) (hG : IsConnectedReductive G),
  letI : IsAffineHom G.X.hom := hG.isAffineHom
  ∀ B : ValuationBuildingData G,
    ∃ (C : MaximalUnramified.BuildingData F (baseChanged F (inertiaFixedField F) G))
      (D : MaximalUnramified.SemilinearApartmentData C)
      (e : B.ReducedBuilding → C.ReducedBuilding)
      (a : B.Apartment →ᵃ[ℝ] C.Apartment),
      Function.Injective e ∧
      (∀ (g : rationalPoints G) (z : B.ReducedBuilding),
        e (g • z) = rationalExtend F (inertiaFixedField F) G g • e z) ∧
      (∀ w : B.Apartment, e (B.apartmentMap w) = C.apartmentMap (a w)) ∧
      (∀ (σ : inertiaFixedField F ≃ₐ[F] inertiaFixedField F) (z : B.ReducedBuilding),
        D.action σ (e z) = e z) ∧
      (∀ y : C.ReducedBuilding,
        (∀ σ : inertiaFixedField F ≃ₐ[F] inertiaFixedField F, D.action σ y = y) →
          ∃ z : B.ReducedBuilding, e z = y) ∧
      (∀ z : B.ReducedBuilding, C.IsSpecialPoint (e z) → B.IsSpecialPoint z) ∧
      (∀ w : B.Apartment,
        a ⁻¹' AffineRootSystem.facet C.affineRoots (a w) =
          AffineRootSystem.facet B.affineRoots w) ∧
      ∀ s ∈ characterValuationKernel (MaximalUnramified.valuation F)
          (baseChanged F (inertiaFixedField F) B.S.toGrp),
        ∀ w : B.Apartment,
          rationalPoints.map
              ((GroupScheme.baseChange (baseMap F (inertiaFixedField F))).map B.i) s •
            e (B.apartmentMap w) = e (B.apartmentMap w)
```

In words: let `L` be the maximal unramified extension of a nonarchimedean
local field `F` and `G` a connected reductive group over `F`. For all
valuation building data `B` of `G` there are building data `C` of `G_L` with a
semilinear Galois action `D`, a map `e` from the building of `B` to the
building of `C` and a real affine map `a` between their apartments such that
`e` is injective and `G(F)`-equivariant, maps the apartment of `B` by `a` into
the apartment of `C`, has image exactly the Galois-fixed points, reflects
special points, matches the facets of the two apartments along `a`, and the
bounded part `S(L)^1` of the maximal split torus fixes the image of the
apartment of `B`.

## Proof

The Lean proof is the single application

```
unramifiedApartmentDescentReduction specialTorusExistence unramifiedValuationDescent
  valuationBuildingApartmentAxioms chapterSevenBuildingAxioms unramifiedGaloisFixedBuildingPoint
  unramifiedAffineRootRestriction
```

of `unramifiedApartmentDescentReduction` (module
`Geometry.Building.UnramifiedApartmentDescentReduction`), whose type
`UnramifiedApartmentDescentReductionStatement.{u}` is the implication from six
statements to the target. Each is discharged by a theorem proved in the
Library without hypotheses:

1. `specialTorusExistence` (module `Geometry.Building.SpecialTorusExistenceProof`):
   KP Proposition 9.3.4, special tori exist.
2. `unramifiedValuationDescent` (module
   `Geometry.Building.UnramifiedValuationDescentProof`): descent of the
   valuation class from `L` to `F`.
3. `valuationBuildingApartmentAxioms` (module
   `Geometry.Building.ValuationBuildingApartmentAxiomsProof`): every valuation
   building datum satisfies V 7 and AS 2–AS 5.
4. `chapterSevenBuildingAxioms` (module
   `Geometry.Building.ChapterSevenBuildingAxiomsProof`): the Chapter 7 building
   satisfies the Section 4.2 axioms.
5. `unramifiedGaloisFixedBuildingPoint` (module
   `Geometry.Building.UnramifiedGaloisFixedBuildingPointProof`): every
   Galois-fixed point of the building over `L` is a `G(F)`-translate of a
   Galois-fixed point of the apartment.
6. `unramifiedAffineRootRestriction` (module
   `Geometry.Building.UnramifiedAffineRootRestrictionProof`): the relative
   affine roots are the nonconstant restrictions of the absolute ones (KP
   Proposition 9.4.28).

Inside the reduction, the compatible class over `L` is chosen and descended,
the descended class is identified with the apartment of `B`, and the eight
clauses are assembled; the details are on the page of
`Geometry.Building.UnramifiedApartmentDescentReduction`. The statement is not
modified and no hypothesis is added.

## Declarations

- `Langlands.Geometry.Building.unramifiedApartmentDescent :
  UnramifiedApartmentDescentStatement.{u}`.

## Literature

T. Kaletha and G. Prasad, *Bruhat–Tits Theory: A New Approach* (2023),
Chapter 9: §9.2.3, printed p. 326, the building `B = B(G_K)^Γ` with its
apartments; Theorem 9.2.7, printed p. 329, `B` is a building on which `G(k)`
acts; Theorem 9.6.5, printed p. 366, and §9.6.6, printed p. 367, the
identification with the building of the valuation class; Proposition 9.9.2,
printed p. 380, a point of `B(G)` that is special in `B(G_K)` is special in
`B(G)`. The further correspondence of the clauses with the book is on the
statement's page.
