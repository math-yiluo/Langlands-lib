# Base change of Galois pinning data to an intermediate field

This module provides the transport part of the transfer clause for the Tits obstruction
(Task 7603, clause 3). For a scalar tower `k ⊆ E ⊆ K` and Galois pinning data `d` of a
group `G` over `k` with splitting field `K`, it constructs Galois pinning data of `G_E`
over the same field `K`. It also gives the transport of integral weights, proves that the
transport is compatible with the root datum, the base and the star actions of
`Gal(K/E) ⊆ Gal(K/k)`, and gives the underlying actual isomorphisms `G_K ≅ (G_E)_K` and
`T_K ≅ (T_E)_K`. Nothing here uses simple connectedness, a Tits index, finiteness of `E/k`
or separability.

## Generic tower lemmas (namespace `StarActionFiniteStage`)

Schemes `B ← SL ← SK` with `bL : SL ⟶ B`, `j : SK ⟶ SL`, `bK = j ≫ bL`, and a
commutative group scheme `T` over `B`. `towerIsoOf bL j T bK hc : T_{SK} ≅ (T_{SL})_{SK}` is
the Library's tower isomorphism (`Reductive/StarActionFiniteStageTower`).

* `descentPoint_towerIsoOf_inv`: for an endomorphism `a` of `SK` over `SL` (so also over
  `B`), the inverse tower isomorphism carries the change of test-scheme structure along
  `a` for `(T_{SL})_{SK}` to that for `T_{SK}`. This is the Library's
  `descentPoint_comp_of_fst` for the comparison map `(baseChangeCompIso bL j T).inv`, whose
  projection to `T` is computed by `baseChangeCompIso_inv_fst`.
* `transport_congr_towerIsoOf`: tower compatibility of transports. Under
  `characterLattice.congr (towerIsoOf …)`, the Library's character transport along `a` over
  `SL` (for `T_{SL}`) equals the character transport along `a` over `B` (for `T`). Proof:
  extensionality on points (`characterLattice.ext_points`), the point formula
  `characterLattice.transport_points` on both sides and the previous lemma.
* `towerIsoOf_hom_naturality`: the tower isomorphism is natural in `T`. This is the
  Library's `baseChangeCompIso_hom_naturality` read in the additive category of commutative
  group schemes.
* `starAction_comp_of_weightMap_of_fields`: if an equivalence `e` of the root data of two
  Galois pinning data carries one base onto the other and intertwines the Galois actions of
  `σ` and `τ` on characters, then it intertwines their star actions. The two data may
  have different ground fields, splitting fields and groups. The proof is that of the
  Library's `StarActionFiniteStage.starAction_comp_of_weightMap`, which assumes a common
  ground field. Only the ground field is generalized.

## The field tower `k ⊆ E ⊆ K`

Fields `k, E, K` with `Algebra k E`, `Algebra k K`, `Algebra E K` and `IsScalarTower k E K`.
An intermediate field `E` of `K/k`, seen as a type, is the main example.

* `algebraBaseMap_comp_algebraBaseMap`: `Spec K → Spec E → Spec k` is `Spec K → Spec k`.
* `torusTowerIso k E K T : T_K ≅ (T_E)_K` for a commutative group scheme `T` over `k`, and
  `groupTowerIso k E K G : G_K ≅ (G_E)_K` for a group scheme `G` over `k`. Both are the
  actual base-change composition isomorphisms. `torusTowerIso_square`: they commute with
  the base changes of a homomorphism `T → G`. `baseChange_map_eq_groupTowerIso`: the
  two-step base change of a homomorphism is its one-step base change conjugated by the
  group tower isomorphisms.
* `characterTowerEquiv k E K T : X^*(T_K) ≃ₗ[ℤ] X^*((T_E)_K)`, `χ ↦ (torusTowerIso).inv ≫ χ`,
  for any commutative group scheme `T` over `k`.
  * `characterTowerEquiv_comp`: naturality. For `τ : T' ⟶ T` over `k`, the transport of
    `τ_K ≫ χ` is `(τ_E)_K ≫` (the transport of `χ`).
  * `characterTowerEquiv_galoisRepresentation`: Galois compatibility. For
    `σ : K ≃ₐ[E] K`, the transport carries the Library's Galois action of
    `σ.restrictScalars k` on `X^*(T_K)` (through the `k`-structure of `T`) to the Galois
    action of `σ` on `X^*((T_E)_K)` (through the `E`-structure of `T_E`). This is
    `transport_congr_towerIsoOf` with `a = Spec σ`.

## Base change of Galois pinning data (namespace `GaloisPinningData`)

Let `G` be an affine group scheme over `Spec k` and `d : GaloisPinningData k K G` (Library,
`Reductive/StarAction`).

* Instances: `G_E` is affine (`baseChangeIsAffineHom`), and it is locally of finite type when
  `G` is (`baseChangeLocallyOfFiniteType`).
* `baseChange d E : GaloisPinningData E K G_E`, with `G_E = (GroupScheme.baseChange
  (algebraBaseMap k E)).obj G`. Its fields:
  * torus `T_E`, and inclusion the base change of the inclusion of `T` (`baseChange_torus`,
    `baseChange_inclusion`, both `rfl`);
  * connected reductivity of `(G_E)_K` (`baseChange_isConnectedReductive`), splitness of
    `(T_E)_K` (`baseChange_isSplitTorus`) and maximality (`baseChange_isMaximalTorus`),
    all transported from `d` along `groupTowerIso` and `torusTowerIso` by the Library's
    `IsConnectedReductive.of_iso`, `IsSplitTorus.of_iso` and
    `IsMaximalTorus.of_eq_iso_comp_comp_iso`;
  * the same root index type, the root datum `baseChangeRootDatum` (Library
    `torusTransportRootDatum` along `torusTowerIso`), its realization on `(G_E)_K`
    (`baseChange_isRootDatum`, Library `IsRootDatumOf.torusTransport` with
    `torusTowerIso_square`), reducedness, and the transported base `baseChangeBase`;
  * simple-root Lie vectors chosen by the Library's `RootPinning.ofSplitMaximalTorus`. They
    are not transported from `d`. The star action, the root datum and the base do not
    depend on them.
* `weightTransport d E : X^*(T_K) ≃ₗ[ℤ] X^*((T_E)_K)`, the integral weights of `d` to those of
  `baseChange d E`. It is `characterTowerEquiv k E K d.torus`.
* `baseChangeRootDatumEquiv d E`: the equivalence of root data, Library
  `torusTransportRootDatumEquiv`, with weight map `weightTransport` and identity on root
  indices (`baseChangeRootDatumEquiv_weightMap`, `baseChangeRootDatumEquiv_indexEquiv`).
  Further compatibilities:
  * `baseChange_base_support`, `mem_baseChange_base_support_iff`: the base keeps its
    simple-root indices.
  * `weightTransport_root`: roots go to the roots with the same index.
  * `baseChange_coroot`: the coroots of the base change are the transported coroots.
  * `pairing_weightTransport_coroot`: the pairing of a weight with each coroot is
    unchanged. In particular dominance is preserved.
* Star compatibility. `baseChangeRootDatumEquiv_comp_starAction`: for `σ : K ≃ₐ[E] K`,
  `e ∘ ⋆_d(σ|_k) = ⋆_{d_E}(σ) ∘ e` as equivalences of root data, where
  `e = baseChangeRootDatumEquiv d E` and `σ|_k = σ.restrictScalars k`. The proof applies
  `starAction_comp_of_weightMap_of_fields` with `characterTowerEquiv_galoisRepresentation`.
  `baseChange_starAction_weightTransport` is the same identity on weights:
  `⋆_{d_E}(σ) (weightTransport λ) = weightTransport (⋆_d(σ|_k) λ)`.
* `forall_fixingSubgroup_starAction_iff`: for an intermediate field `F` of `K/k`, a weight
  `λ` is fixed by the star action of every element of `F.fixingSubgroup` if and only if
  `weightTransport λ` is fixed by the full star action of `baseChange d F`. The converse
  direction uses Mathlib's `IntermediateField.fixingSubgroupEquiv`, which identifies
  `F.fixingSubgroup` with `K ≃ₐ[F] K`, and injectivity of the transport.

Remark, not formalized in this module: if `K` is a separable closure of `k`, it is also a
separable closure of every intermediate field `E`. In that case `baseChange d E` is Galois
pinning data of `G_E` over a separable closure of `E`.

## Provenance

Internal. These are compositions of Library results: the base-change composition
isomorphisms and their tower lemmas, transport of root data along torus isomorphisms, the
descent-point comparison, the iso-invariance of reductivity, splitness and maximality, and
the root-line theorem. Mathematically, the star compatibility is the identification of the
`*`-action of `G` over an intermediate field with the restriction of the `*`-action of `G`
over `k`. Tits (1971), Proposition 5.1, uses it implicitly when it compares `β_{G,k}` with
`β_{G,k₁}`. The proof given here works directly with the actual base-change
isomorphisms.

The comparison across ground fields applies `GaloisPinningData.starAction_comp_of_character_intertwining` to the two pinnings and their weight equivalence.
