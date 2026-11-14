# Restriction of pinned roots to a maximal split torus

Author: Worker 4348.

Module `Langlands.GroupScheme.Rational.CompatiblePinningRestriction`, namespace
`Langlands.GroupScheme.GaloisCompatiblePinningData`.

## Setting

- `k ⊆ K` are fields, `G` is an affine group scheme over `Spec k`, and
  `D : GaloisCompatiblePinningData k K G` is the published structure of module
  `Rational.QuasiSplitCompatiblePinning`. It provides:
  - a split pinning `p = D.pinning` of `G_K`;
  - a torus `D.torus` over `k` with `D.inclusion : D.torus ⟶ G`;
  - an isomorphism `D.torusIso : p.torus ≅ (D.torus)_K` with `p.inclusion` equal to `D.torusIso`
    followed by the base change of `D.inclusion` (`D.inclusion_eq`);
  - an action `D.action` of `Γ = Aut_k(K)` on the simple roots, compatible with the Galois
    action on characters (`D.action_root`).
- `t : S ⟶ D.torus` is a map from a torus `S` over `k`. In the application
  `groupHom t ≫ D.inclusion` is a maximal split torus of `G`, and `D.inclusion` represents its
  centralizer.
- `a_K` is `characterLattice.baseChange (algebraBaseMap k K) S a`.

## Definitions

- `restrictMap t = t_K ≫ D.torusIso.inv : S_K ⟶ p.torus`. Restricting a root `r` of the
  pinning to `S_K` means forming `restrictMap t ≫ p.rootDatum.root r`.
- `transportedRootDatum`: the root datum of the pinning moved to the base-changed descended
  torus along `D.torusIso`, using the published `torusTransportRootDatum`. It has the same
  index type, and its roots are `characterLattice.congr D.torusIso` of the pinned roots
  (`transportedRootDatum_root`).

## Results

- `groupHom_restrictMap_comp_inclusion`: `groupHom (restrictMap t) ≫ p.inclusion` equals the
  base change of `groupHom t ≫ D.inclusion`. Proof: `D.inclusion_eq` and
  `D.torusIso.inv_hom_id`.
- `restrictMap_comp_root r`: `restrictMap t ≫ root r = t_K ≫ transportedRootDatum.root r`.
- `transportedRootDatum_isRootDatum`: the transported datum is a root datum of the base change
  of `D.inclusion`. This is the published `IsRootDatumOf.torusTransport`.
- `transportedRootDatum_action_root σ a`: the transported root of `D.action σ a` is the
  Galois transform of that of `a`. This restates `D.action_root`.
- `restrictMap_comp_root_action hS σ a`: if `S` is split, `restrictMap t ≫ root (D.action σ a)`
  equals `restrictMap t ≫ root a`. Proof: write the restriction as a base change
  (`characterLattice.baseChangeEquiv`, surjective for split `S`), then use
  `galoisRepresentation_precompose` and `galoisRepresentation_baseChange`.
- `transportedRoot_mem_roots r`: transported roots are roots of the base change of
  `D.inclusion`.
- `exists_relativeRoot_restrict hS hT hcent r`: assume `S` and `(D.torus)_K` split, and
  `D.inclusion` representing the centralizer of `groupHom t ≫ D.inclusion`. Then every root
  `r` restricts to `a_K` for some relative root `a` of `groupHom t ≫ D.inclusion`. Proof:
  - the restriction is nonzero (`root_restrict_ne_zero_of_torusCentralizer`);
  - it is a base change of some `a`, and is a root of the base-changed composite
    (`mem_roots_comp_iff`);
  - so `a` is a relative root (`mem_roots_baseChange_iff`).
- `exists_galois_of_restrict_eq hS hT hf hjc hcent h`: let `K/k` be finite Galois and the
  composite a maximal split torus. If two roots `r`, `r₀` of the pinning have the same
  restriction, then for some `σ ∈ Γ` the transported root of `r` is the Galois transform of
  that of `r₀`. This is the published `rootOrbit_eq_restrictionFiber_of_torusCentralizer`
  (restriction fibres are Galois orbits), applied to the transported root datum.
- `exists_action_eq_of_restrict_eq …`: if `r` has the restriction of a simple root `a₀`, then
  `r = D.action σ a₀` for some `σ`. This combines the previous result with
  `transportedRootDatum_action_root` and injectivity of roots.
- `restrictsToMultipliableLine hS hT hcent hE a`: under `[Smooth G.X.hom]` and a monomorphism
  instance for the composite, suppose the composite has opposite factor pairs (`hE`). Then
  `RestrictsToMultipliableLine (restrictMap t) p.rootDatum a_K` holds: a root restricting to
  `n • a_K` has `n ∈ {±1, ±2}`. Proof: `n • a` is a relative root, as in
  `exists_relativeRoot_restrict`; then apply the published
  `HasOppositeFactorPairs.eq_one_or_two_of_nsmul_mem` to `n` or `-n`. This copies the
  argument of the published apartment-existence proof
  (`torusFieldRestrictedRootFunctionFamily_opposite_of_two_mem`).

## Provenance

This module is internal glue between the published compatible-pinning data, root-datum
transport, and the Galois description of restriction fibres. It makes no new mathematical
assertion. It supports the `A₂`-orbit case of `Z(k) ⊆ G(k)^+` for quasi-split simply
connected groups.
