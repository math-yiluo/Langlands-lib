# Existence of a comparison of building data over `F` and `K = F^ur` (KP §9.6, §9.8)

Module: `Langlands.Geometry.Building.KPUnramifiedComparisonExistenceStatement`.

Declaration: `Langlands.Geometry.Building.UnramifiedComparisonExistenceStatement`, a
`def` returning `Prop`, universe polymorphic in `u`.

**This module states a proposition; it does not prove it.** No theorem of the Library proves
`UnramifiedComparisonExistenceStatement`, and this module does not assume it anywhere.

## The statement

```lean
def UnramifiedComparisonExistenceStatement : Prop :=
  ∀ (F : Type u) [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]
    (G : GroupScheme (Spec (CommRingCat.of F))) [IsAffineHom G.X.hom]
    (P : ParahoricBuildingData G), P.SatisfiesApartmentAxioms →
      ∃ (B : MaximalUnramified.BuildingData F (baseChanged F (UnramifiedClosure F) G))
        (hZ : IsTorus B.centralizer.Z) (e : P.Apartment → B.Apartment),
        P.IsUnramifiedComparison B hZ e
```

In words: let `F` be a nonarchimedean local field (equal or mixed characteristic), `G` a group
scheme over `Spec F` with affine structure morphism, and `P : ParahoricBuildingData G`
building data of `G` over `F` (maximal split torus `S`, centralizer `Z`, apartment class
`P.apartment`) satisfying the apartment axioms. Write `K = UnramifiedClosure F` and
`G_K = baseChanged F K G`. Then there exist

- building data `B : MaximalUnramified.BuildingData F G_K` of `G_K` over `K`,
- a proof `hZ` that the centralizer `B.centralizer.Z` of the maximal `K`-split torus `B.S`
  is a torus,
- a map `e : P.Apartment → B.Apartment` from the apartment of `S` to the apartment of `B.S`,

such that `(B, hZ, e)` is a comparison of `P` with `K`, that is,
`P.IsUnramifiedComparison B hZ e` holds. That Prop-valued structure and its per-root part
`IsUnramifiedRootComparison` are published in module `KPUnramifiedMoyPrasadComparison`. The
statement adds no hypothesis beyond `P.SatisfiesApartmentAxioms` and the instances above. In
particular it assumes no splitness, quasi-splitness, tameness or residue-characteristic
condition.

The private instance at the top of the module derives `IsAffineHom` for
`baseChanged F K G → Spec K` by base change from `[IsAffineHom G.X.hom]`. It adds no
hypothesis: it is the same argument as the private instances of
`KPUnramifiedRationalMoyPrasadStatement` and `KPUnramifiedMoyPrasadComparison`.

## Role in KP §9.8

The body is exactly the hypothesis `hC` of the published theorem

```lean
theorem unramifiedRationalMoyPrasad_of_unramifiedComparison
    (hS2 : MaximalUnramified.LocalMoyPrasadGroupPropertiesStatement.{u})
    (hC : ...) : UnramifiedRationalMoyPrasadStatement.{u}
```

(module `KPUnramifiedMoyPrasadComparison`). A proof of
`UnramifiedComparisonExistenceStatement.{u}` and a proof of
`MaximalUnramified.LocalMoyPrasadGroupPropertiesStatement.{u}` therefore give
`UnramifiedRationalMoyPrasadStatement.{u}` by
`unramifiedRationalMoyPrasad_of_unramifiedComparison hS2 hC`. The author checked this
application by compiling it in a private draft against this module (environment
`5c94c648-e8dc-4002-a50a-071ebf3f6096`; 0 errors, 0 warnings). The check is not part of the
module. With the published reduction
`ParahoricBuildingData.exists_doubleRootFriendly_filtration_of_rationalMoyPrasadFamily`
(module `KPRationalMoyPrasadFamily`), that statement in turn gives KP Lemma 9.8.1 in the form
`CentralizerFiltrationDoubleRootExistenceStatement`.

## What the statement asserts, field by field

Write `ι = rationalExtend F K G : G(F) → G(K)` and
`j = rationalPoints.map P.centralizer.j : Z(F) → G(F)`. The KP sources below are those of the
published Markdown of `KPUnramifiedMoyPrasadComparison`, which gives the full argument for
each field. In the intended instance `B` is attached to a special torus `T ⊇ S`, with
`B.S = T_K` (see the next section).

`IsUnramifiedComparison P B hZ e`:

| Field | Assertion | KP source |
| --- | --- | --- |
| `apartmentMap_smul` | `B.apartmentMap (e (n • y)) = ι(n) • B.apartmentMap (e y)` in the reduced building of `G_K`, for `n ∈ N(F)`, `y ∈ A(S)`. | Equivariance under `N(k)` in Theorem 9.6.5 (printed p. 366, PDF p. 397). |
| `rootComparison` | For each relative root `a` of `(G, S)` there are `Ψ, ν` with `IsUnramifiedRootComparison P B e a Ψ ν` (table below). | §9.8.2, Lemma 9.6.3, Proposition 9.8.3. |
| `levi` | Some `ν` has `ι(j(Z(F))) ⊆ M_ν(K)` and `(e y).val b = (e y').val b` for all `y, y'` and all `b` with `⟨b, ν⟩ = 0`. | `A(S) = A(T_K)^Γ` is an affine space under `V(S)` (§9.6, §9.8.2); `ν` generic in the image of `V(S)`. |
| `comap_zero` | `j⁻¹(ι⁻¹(G(K)_{e y,0})) = Z(F)^0` (`P.centralizerZero`) for every `y`. | First paragraph of the proof of Lemma 9.8.1 (printed p. 375, PDF p. 406), with Definition 2.6.23(2) (printed p. 104, PDF p. 135), Proposition 9.3.24 (printed p. 343, PDF p. 374) and Corollary 9.7.3(2) (printed p. 370, PDF p. 401). |
| `isOpen` | Each `j⁻¹(ι⁻¹(G(K)_{e y,r}))` is open in `Z(F)` for the rational-point topology. | Proposition 9.8.3(2) with Corollary 7.3.14 (printed p. 251, PDF p. 282). |

`IsUnramifiedRootComparison P B e a Ψ ν` (in the intended instance `Ψ` is the set of relative
roots of `(G_K, T_K)` restricting to `a` or `2a`, and `ν` is a generic point of the image of
`V(S)` with `⟨a, ν⟩ > 0`):

| Field | Assertion | KP source |
| --- | --- | --- |
| `closed` | `Ψ` is a closed set of relative roots of `B`. | Remark 9.6.4 (printed p. 366, PDF p. 397). |
| `pos` | `⟨b, ν⟩ > 0` for `b ∈ Ψ`. | `⟨b, ν⟩ = ⟨b|_S, ν⟩`. |
| `root_mem` | `ι(U_a(F)) ⊆ U_Ψ(K)`. | Proof of Lemma 9.6.3 (printed p. 366, PDF p. 397). |
| `neg_mem` | `ι(U_{-a}(F))` lies in the span of the `U_b(K)` with `⟨b, ν⟩ < 0`. | The same, for `-a`. |
| `levi_mem` | `ι(j(Z(F))) ⊆ M_ν(K)`. | `M_ν = Z_K` for generic `ν`; generation of `Z_K(K)` by `Z_{G_K}(T_K)(K)` and the root groups of `(Z_K, T_K)`. |
| `filtration_mem` | `ι(U_{a,y,s}) ⊆ ⟨U_{b,e y,s} ∣ b ∈ Ψ⟩` for `s ≥ 0`. | Lemma 9.6.3, inclusion `⊆`, via `A(S) ⊂ A(T_K)` (§9.8.2). |
| `block_mem` | `g ∈ U_a(F)` and `ι g ∈ ⟨U_{b,e y,t} ∣ b ∈ Ψ⟩` imply `g ∈ U_{a,y,t} U_{2a,y,t}`. | Proposition 9.8.3(1) and its proof (printed pp. 375–376, PDF pp. 406–407), with §9.8.2 and Definition 7.3.3(1). |

The groups `G(K)_{x,r}` are D1's `MaximalUnramified.BuildingData.moyPrasad`
(module `KPLocalMoyPrasadGroups`). The `K`-side spans are those of
`KPLocalMoyPrasadGroupProperties` (`rootGroupSpan`, `rootFiltrationSpan`, `pairingLeviSpan`,
`negativePairingRoots`, `zeroPairingRoots`, `IsClosedRootSet`).

## Intended proof (not formalized here)

KP §9.8.2 fixes the comparison as follows. This is guidance for a proof, not part of the
statement.

1. Choose a special `F`-torus `T ⊇ S`, i.e. `T_K` is a maximal `K`-split torus of `G_K`
   (Proposition 9.3.4, printed p. 332, PDF p. 363). Library:
   `SpecialTorusExistenceStatement` (module `UnramifiedSpecialApartmentStatement`), published
   as a statement; its proof is Task 5514.
2. Take for `B` building data of `G_K` relative to `T_K`, with its V 6 class. Library: the
   proved theorem `quasiSplitIntegerApartmentExistence`
   (`QuasiSplitIntegerApartmentExistenceProof`). `G_K` is quasi-split (Steinberg), so the
   centralizer of `T_K` is a torus, which gives `hZ`.
3. Descend the valuation class: KP Construction 9.6.1, Lemma 9.6.3 and Theorem 9.6.5
   (printed pp. 364–366, PDF pp. 395–397). Library: `UnramifiedValuationDescentStatement`
   (module `UnramifiedValuationDescentStatement`), published as a statement; its proof is
   Task 5553. Its last clause is the building-form normalizer relation that
   `apartmentMap_smul` asks for. The proved theorem `omegaCompatibleApartmentUniqueness`
   (`OmegaCompatibleApartmentUniquenessProof`, KP Proposition 6.2.6) identifies the descended
   class with `P.apartment` (printed p. 216, PDF p. 247). `e` is the inverse of this identification, i.e. the inclusion
   `A(S) ⊂ A(T_K)`.
4. The root fields follow from the description of `U_a(F)` and of its filtration inside
   `∏_b U_b(K)` (proof of Lemma 9.6.3, Proposition 9.8.3(1)). `levi` follows from the affine
   structure of `A(S)` over `V(S)`.

Points a proof will need beyond the Library's present content (as far as the author can see):

- **Depth zero (`comap_zero`).** D1's zero term of the centralizer filtration is the norm
  Iwahori subgroup `torusNormIwahori` of `Z(K)`, and `P.centralizerZero` is defined through
  `ZeroSubgroupDatum.centralizerZero` (module `KPZeroSubgroups`). Comparing
  `ι⁻¹(G(K)_{e y,0}) ∩ j(Z(F))` with `Z(F)^0 = Z(K)^0 ∩ Z(F)` (Definition 2.6.23(2)) may need
  its own statement and proof.
- **Generation of `Z_K(K)`** by `Z_{G_K}(T_K)(K)` and root groups (`levi_mem`, `levi`).
- **Descent of filtrations and blocks** (`filtration_mem`, `block_mem`).
- **Openness** (`isOpen`).

## Provenance

Derived. KP do not state this proposition as one result. It packages, for the comparison
interface `IsUnramifiedComparison` (an internal interface; see the Markdown of
`KPUnramifiedMoyPrasadComparison`), the existence of the comparison that KP set up in §9.8.2
from a special torus (Proposition 9.3.4) and the descent of Construction 9.6.1, Lemma 9.6.3
and Theorem 9.6.5, together with the facts proved or used in Lemma 9.8.1 and
Proposition 9.8.3. Its binders and witnesses are those of the published
`UnramifiedRationalMoyPrasadStatement` (module `KPUnramifiedRationalMoyPrasadStatement`),
with the conclusion `IsRationalMoyPrasadFamily` replaced by `IsUnramifiedComparison`.

## Sources

- Tasho Kaletha and Gopal Prasad, *Bruhat–Tits Theory: A New Approach* (2023), registered
  source `kaletha-prasad-2023-bruhat-tits-new-approach`, SHA-256
  `05ad9a284a2577b34d1a270228b74dfb28f520561ae7772d8f38dddb78938732`:
  - Proposition 9.3.4 (printed p. 332, PDF p. 363);
  - Proposition 9.3.24, `G(k)^0 = G(K)^0 ∩ G(k)` (printed p. 343, PDF p. 374);
  - Construction 9.6.1, Remark 9.6.2, Lemma 9.6.3, Remark 9.6.4 and Theorem 9.6.5 (printed
    pp. 364–366, PDF pp. 395–397);
  - Corollary 9.7.3 (printed p. 370, PDF p. 401);
  - §9.8, Lemma 9.8.1, §9.8.2 and Proposition 9.8.3 (printed pp. 374–376,
    PDF pp. 405–407);
  - Definition 7.3.3 (printed p. 247, PDF p. 278) and Corollary 7.3.14 (printed p. 251,
    PDF p. 282);
  - Definition 2.6.23(2) (printed p. 104, PDF p. 135);
  - Proposition 6.2.6 (printed p. 216, PDF p. 247).
- Kaletha and Prasad, *Corrections and additions to Bruhat–Tits theory, a new approach*
  (2024), registered source `kaletha-prasad-2024-corrections`, SHA-256
  `23293f51e58d5ceecb91f834743f68058b98431797d2531142415d013fdf61ed`, PDF pp. 39–41
  (Chapter 9 corrections, including the proof of Lemma 9.8.1).
