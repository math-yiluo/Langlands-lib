# Galois stability and descent of the unramified zero subgroups

Lean module: `Langlands.Geometry.Building.UnramifiedZeroDescentProof`,
namespace `Langlands.Geometry.Building`.

This module proves `Langlands.Geometry.Building.UnramifiedZeroDescentStatement`
(module `Langlands.Geometry.Building.UnramifiedZeroDescentStatement`): KP
Proposition 9.3.24 together with the Galois stability of `G(K)^1` and of the
zero subgroups `G(K)^0` over the maximal unramified extension `K`.

## Statements

```
theorem Langlands.Geometry.Building.unramifiedZeroDescent_of_geometric_inputs
    (hExists : ValuationApartmentAxiomsExistenceStatement.{u})
    (hDescent : UnramifiedApartmentDescentStatement.{u}) :
    UnramifiedZeroDescentStatement.{u}

theorem Langlands.Geometry.Building.unramifiedZeroDescent :
    UnramifiedZeroDescentStatement.{u}
```

The type of `unramifiedZeroDescent` is exactly the published proposition, at
an arbitrary universe `u`, with no further hypothesis. Unfolded, it reads:

```
∀ (F : Type u) [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  (G : GroupScheme (Spec (CommRingCat.of F))), IsConnectedReductive G →
  (∀ σ : UnramifiedClosure F ≃ₐ[F] UnramifiedClosure F,
    ∀ x ∈ characterValuationKernel (MaximalUnramified.valuation F)
        (baseChanged F (UnramifiedClosure F) G),
      rationalConjugate F (UnramifiedClosure F) G σ x ∈
        characterValuationKernel (MaximalUnramified.valuation F)
          (baseChanged F (UnramifiedClosure F) G)) ∧
  ∀ E : UnramifiedZeroDatum F (baseChanged F (UnramifiedClosure F) G),
    (∀ σ : UnramifiedClosure F ≃ₐ[F] UnramifiedClosure F,
      ∀ x ∈ E.zeroPoints,
        rationalConjugate F (UnramifiedClosure F) G σ x ∈ E.zeroPoints) ∧
    ∀ {S : CommGroupScheme (Spec (CommRingCat.of F))}
      {Z : GroupScheme (Spec (CommRingCat.of F))}
      (i : S.toGrp ⟶ G) (j : Z ⟶ G) (Z0 : ZeroSubgroupDatum i j),
      E.zeroPoints.comap (rationalExtend F (UnramifiedClosure F) G) = Z0.zeroSubgroup
```

In words: let `K` be the maximal unramified extension of a nonarchimedean
local field `F` and `G` a connected reductive group over `F`. (1) Every
`σ ∈ Aut(K/F)` maps `G(K)^1`, the points on which every `K`-rational character
has valuation zero, into itself. (2) For every zero datum `E` of `G_K`
(Definition 2.6.23(1)), `σ` maps `G(K)^0 = E.zeroPoints` into itself. (3) For
every such `E` and every zero datum `Z0` over `F`, the `F`-points of `G` lying
in `G(K)^0` form exactly `G(F)^0 = Z0.zeroSubgroup`.

The module also contains two private lemmas,
`galoisStable_characterValuationKernel` and `galoisStable_zeroPoints`, which
state clauses (1) and (2) with the text of the statement.

## Proofs

`unramifiedZeroDescent_of_geometric_inputs` proves the statement from
`ValuationApartmentAxiomsExistenceStatement` and
`UnramifiedApartmentDescentStatement`:

1. Clause (1) is `unramified_characterValuationKernel_galois_iff` (module
   `Geometry.Building.UnramifiedCharacterValuationKernelGaloisStability`), the
   implication from `x ∈ G(K)^1` to `σ · x ∈ G(K)^1`.
2. Clause (2) is `UnramifiedZeroDatum.rationalConjugate_mem_zeroPoints`
   (module `Geometry.Building.UnramifiedZeroPointsGaloisStability`), applied
   to each datum `E`.
3. Clause (3) is `unramifiedZeroDescentGeometricReduction` (module
   `Geometry.Building.UnramifiedZeroGeometry`), applied to the two hypotheses
   and to `MaximalUnramified.zeroFacetNoInversions` (module
   `Geometry.Building.UnramifiedZeroFacetNoInversionsProof`), proved without
   hypotheses.

Clauses (1) and (2) use neither hypothesis. In the elaborated statement some
instance arguments are auxiliary proof terms of the statement's definition,
while the two private lemmas carry the instance proofs themselves; the proof
matches each lemma against its clause with `convert … using 0`, which compares
these proof arguments by proof irrelevance.

`unramifiedZeroDescent` applies `unramifiedZeroDescent_of_geometric_inputs`
to `valuationApartmentAxiomsExistence` (module
`Geometry.Building.ValuationApartmentAxiomsExistenceProof`) and
`unramifiedApartmentDescent` (module
`Geometry.Building.UnramifiedApartmentDescentProof`), both proved without
hypotheses.

## Declarations

- `galoisStable_characterValuationKernel` (private);
- `galoisStable_zeroPoints` (private);
- `Langlands.Geometry.Building.unramifiedZeroDescent_of_geometric_inputs`;
- `Langlands.Geometry.Building.unramifiedZeroDescent :
  UnramifiedZeroDescentStatement.{u}`.

## Literature

T. Kaletha and G. Prasad, *Bruhat–Tits Theory: A New Approach* (2023):
Chapter 9, §9.3, Proposition 9.3.24, printed p. 343: `G(k)^0 = G(K)^0 ∩ G(k)`;
Chapter 2, §2.6, Remark 2.6.26, printed p. 105, on the definition of `G(k)^0`.
The authors' *Corrections and additions* (version of 1 November 2024), p. 40,
replace the first lines of the proof of Proposition 9.3.24 and leave its
statement unchanged. The correspondence of clauses (1) and (2) with the book
is on the statement's page.
