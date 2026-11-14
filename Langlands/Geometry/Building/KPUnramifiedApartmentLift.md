# Concrete special-torus apartment lifts (KP §9.6, §9.8.2)

Module: `Langlands.Geometry.Building.KPUnramifiedApartmentLift`.

This module packages the construction behind KP Construction 9.6.1, Theorem 9.6.5 and
§9.8.2 as Lean data: a special torus `T ⊇ S` and the points of the apartment of `T_K` over
`K = F^ur` that are fixed by `Gal(K/F)` and restrict to the points of `A(S)`. It is a derived
interface. It does **not** assert or prove the existence of an unramified comparison
(`UnramifiedComparisonExistenceStatement`). It contains none of the root, Levi, depth-zero
or openness fields of `ParahoricBuildingData.IsUnramifiedComparison`; those are the four
targets of the sibling module `KPUnramifiedComparisonFieldStatements`.

## Declarations

In namespace `Langlands.Geometry.Building`:

| Declaration | Kind | Status |
| --- | --- | --- |
| `ParahoricBuildingData.UnramifiedComparisonTorus` | structure (data) | definition |
| `ParahoricBuildingData.UnramifiedComparisonTorus.extendedMono` | instance | proved |
| `ParahoricBuildingData.UnramifiedComparisonTorus.upstairsTorus` | abbrev | definition |
| `ParahoricBuildingData.UnramifiedComparisonTorus.upstairsInclusion` | abbrev | definition |
| `ParahoricBuildingData.UnramifiedComparisonTorus.ApartmentLift` | structure (data) | definition |
| `ParahoricBuildingData.UnramifiedComparisonTorus.ApartmentLift.buildingData` | abbrev | definition |
| `ParahoricBuildingData.UnramifiedComparisonTorus.ApartmentLift.centralizer_isTorus` | theorem | proved, unconditional |
| `exists_unramifiedApartmentLift` | theorem | proved, **conditional on two unproved premises** |

A private instance, `unramifiedApartmentLiftAffineHom`, records that the structure morphism
of `G_K` is affine (a base change of an affine morphism). This is the same private-instance
pattern used in the published `KPUnramifiedMoyPrasadComparison`.

## Notation

`F` is a nonarchimedean local field (instances `Field`, `ValuativeRel`, `TopologicalSpace`,
`IsNonarchimedeanLocalField`). `G` is a group scheme over `Spec F` with affine structure
morphism, and `P : ParahoricBuildingData G`. Its maximal split torus is `P.i : P.S → G`,
its apartment is `P.apartment`, and its centralizer is `P.centralizer`. The field
`K = UnramifiedClosure F` is an abbrev for `inertiaFixedField F`. These are definitionally
equal, so the premises below, which are stated with `inertiaFixedField F`, apply directly.
Scalar extension is the Library's base change along `algebraBaseMap F K`.

## `UnramifiedComparisonTorus P`

| Field | Meaning |
| --- | --- |
| `T` | a commutative group scheme over `F` |
| `iT : T → G` | its map to `G` |
| `f : P.S → T`, `factor` | `P.i` factors as `f` followed by `iT`, i.e. `T ⊇ S` for the particular torus `S = P.S` |
| `isClosedSubgroup` | `iT` is a closed subgroup |
| `isMaximalSplitTorus` | `iT_K : T_K → G_K` is a maximal `K`-split torus |

These fields are exactly the conclusion of the published premise
`SpecialTorusExistenceStatement` (KP Proposition 9.3.4), applied to `(P.S, P.i)`. So `T`
is a special `F`-torus containing `S` in the sense of KP §9.2.2 (printed p. 326,
PDF p. 357). The Lean structure, like that statement, does not separately require `T` to be
a torus over `F`; it only requires `T_K` to be a maximal split torus of `G_K`.

- `extendedMono`: `iT_K` is a monomorphism of underlying schemes, by the published
  `mono_of_isMaximalSplitTorus`. The apartment data over `K` need this instance.
- `upstairsTorus` is `T_K` and `upstairsInclusion` is `iT_K : T_K → G_K`.

## `ApartmentLift t` for `t : UnramifiedComparisonTorus P`

Write `ι = rationalExtend F K G : G(F) → G(K)`.

| Field | Meaning | KP source |
| --- | --- | --- |
| `apartment` | a `KPApartmentData` for `(G_K, T_K)` with the order of the integer-valued valuation of `K`: an `N(K)`-stable equipollence class of valuations of the root datum of `(G_K, T_K)`, the `V(T_K)`-orbit of a valuation compatible with that order on `T_K(K)` | the apartment of `T_K` as a class of valuations of the root datum, Remark 9.6.2 (printed p. 365, PDF p. 396) |
| `centralizer` | a `CentralizerDatum` of `T_K` in `G_K` | — |
| `isOmegaCompatible` | `apartment` satisfies V 6 for this centralizer and the integer valuation of `K` | — |
| `oppositeFactorPairs` | `RelativeRoot.HasOppositeFactorPairs` for `iT_K`: every nonidentity rational root point has an opposite factor pair | needed to define the restriction in `restrict` |
| `e : P.Apartment → apartment.Apartment` | a map from `A(S)` to the apartment of `T_K` | the inclusion `A(S) ⊂ A(T_K)` of §9.8.2 (printed p. 376, PDF p. 407) |
| `fixed` | each `e y` is fixed by the coefficient action `RootFunctionFamily.galoisAction` of every `σ ∈ Aut(K/F)` | `A(S)` is the `Γ`-fixed part of the apartment of `T_K` (§9.6 opening, printed p. 364, PDF p. 395); the valuation is `Γ`-invariant (printed p. 366, PDF p. 397) |
| `restrict` | `y.val` is `torusFieldRestrictedRootFunctionFamily` of `(e y).val`, i.e. restriction from `T_K` to `S_K` along `f_K` and then from `K` to `F` | Construction 9.6.1 with Remark 9.6.2 and Lemma 9.6.3 (printed pp. 365–366, PDF pp. 396–397) |
| `normalizer` | `apartment.apartmentMap (e (n • y)) = ι(n) • apartment.apartmentMap (e y)` for `n ∈ N(F)`, in the reduced building of `G_K` | equivariance of `x ↦ φ^x` under `V(S) ⋊ N(k)`, Theorem 9.6.5 (printed p. 366, PDF p. 397) |

The lift keeps the actual special torus, the actual upstairs class and centralizer, the
opposite-factor property, the Galois-fixed map, the restriction to the given downstairs
valuations, and the normalizer compatibility. The normalizer field is stated in the
building, not the apartment of `T_K`, because `N(F)` need not normalize `T_K`. It is the
same equation as the field `apartmentMap_smul` of `IsUnramifiedComparison`. The structure
does not require `e` to be injective or surjective onto the fixed points.

- `buildingData` is the actual upstairs `MaximalUnramified.BuildingData F G_K`: the torus
  `T_K`, the inclusion `iT_K`, its maximality, and `apartment`, `centralizer`,
  `isOmegaCompatible` of the lift. Connected reductivity of `G_K` comes from the published
  theorem `connectedReductiveFieldExtensionStatement`.
- `centralizer_isTorus : IsTorus L.buildingData.centralizer.Z` is **unconditional**. It
  specializes the published `henselianDiscreteQuasiSplit` with
  `unramifiedQuasiSplit_of_henselianDiscrete`, so `G_K` is quasi-split. It then applies the
  published `isTorus_of_quasiSplit_torusCentralizer` with the proved
  `quasiSplitTorusCentralizerExistence` and `maximalSplitTorusConjugacy`. The sibling
  statements use this proof to form the actual Moy–Prasad groups `G(K)_{e y, r}`.

## The conditional theorem `exists_unramifiedApartmentLift`

```lean
theorem exists_unramifiedApartmentLift
    (hSpec : SpecialTorusExistenceStatement.{u})
    (hDesc : UnramifiedValuationDescentStatement.{u})
    ... (P : ParahoricBuildingData G) :
    ∃ t : P.UnramifiedComparisonTorus, Nonempty t.ApartmentLift
```

It depends on exactly two hypotheses, the published unproved proposition targets
`SpecialTorusExistenceStatement` (KP Proposition 9.3.4) and
`UnramifiedValuationDescentStatement` (KP Construction 9.6.1, Lemma 9.6.3,
Theorem 9.6.5). **It proves neither of them.** Every other result it uses is a published
theorem. The proof:

1. `hSpec` applied to `(P.S, P.i)` gives the special torus `t`.
2. The published `UnramifiedBuildingDescent.exists_omegaCompatible`, with quasi-splitness of
   `G_K` (`unramifiedQuasiSplit_of_henselianDiscrete henselianDiscreteQuasiSplit`) and
   `quasiSplitIntegerApartmentExistence`, gives an upstairs class `D` with centralizer `C`
   satisfying V 6.
3. `rootRankOneFactorization` and `RelativeRoot.hasRankOneFactorization_iff_hasOppositeFactorPairs`
   give the opposite-factor property of `iT_K`.
4. `hDesc` gives a downstairs class `DS`, with a centralizer, satisfying V 6. Its members are
   exactly the restrictions of the fixed points of `D`, restriction is injective on fixed
   points, and the normalizer clause holds.
5. The published `omegaCompatibleApartmentUniqueness` identifies `DS` with `P.apartment`.
6. The map `e` and its fields `fixed`, `restrict` and `normalizer` are
   `UnramifiedBuildingDescent.descentPoint`, `.descentPoint_fixed`, `.descentPoint_val` and
   `.descentPoint_normalizer'`. The map `e` is chosen; it is not canonical.

The construction does not use `P.SatisfiesApartmentAxioms`. Existing proof tasks for the two
premises are Task 5514 (special torus) and Task 5553 (valuation descent).

## Provenance

Derived. The structures are internal Lean packaging of the special-torus construction that the
published `KPUnramifiedMoyPrasadComparison.md` names as the intended source of a comparison,
assembled from the published `UnramifiedBuildingDescentReduction`. They introduce no new
mathematical assertion; the only existence claim is the conditional theorem above. The source
is Kaletha–Prasad, *Bruhat–Tits Theory: A New Approach* (2023), registered as
`kaletha-prasad-2023-bruhat-tits-new-approach`, SHA-256
`05ad9a284a2577b34d1a270228b74dfb28f520561ae7772d8f38dddb78938732`:

- §9.2.2, definition of a special `k`-torus (printed p. 326, PDF p. 357);
- Proposition 9.3.4, existence of special tori (printed p. 332, PDF p. 363);
- opening of §9.6, `A(S)` as the `Γ`-fixed points of the apartment of `T_K` (printed p. 364,
  PDF p. 395);
- Construction 9.6.1 and Remark 9.6.2 (printed p. 365, PDF p. 396);
- Lemma 9.6.3 and Theorem 9.6.5 (printed p. 366, PDF p. 397);
- §9.8.2, the inclusion `A(S) ⊂ A(T_K)` (printed pp. 375–376, PDF pp. 406–407).

The Chapter 9 entries of the 2024 corrections (`kaletha-prasad-2024-corrections`, SHA-256
`23293f51e58d5ceecb91f834743f68058b98431797d2531142415d013fdf61ed`, PDF pp. 39–41) concern
the finiteness of `Γ`-orbits and `Γ`-fixed points in §9.2.1, Propositions 9.3.11, 9.3.12,
9.3.13, 9.3.24 and 9.3.25 or their proofs, Proposition 9.4.8, the proof of Lemma 9.8.1, and §9.9. None of
them changes the definition in §9.2.2, Proposition 9.3.4, Construction 9.6.1, Remark 9.6.2,
Lemma 9.6.3, Theorem 9.6.5 or §9.8.2.
