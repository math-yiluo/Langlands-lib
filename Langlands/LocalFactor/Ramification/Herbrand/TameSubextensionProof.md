# Herbrand rescaling across a tame totally ramified subextension: proof

`Langlands.Ramification.HerbrandBridge.tameSubextensionHerbrand` proves
`TameSubextensionHerbrandStatement.{u}` (module
`Langlands.LocalFactor.Ramification.Herbrand.TameSubextension`): for a finite
intermediate field `E` of the algebraic closure of a p-adic field `K`, of
degree `m` prime to `p` and residue degree one,
`relativeHerbrandPsi E v = m v` for `v ≥ 0`, and for `v > 0` the image of
`W_E^{m v}` under `intermediateWeilMap K E` is `W_K^v`.

## Wild inertia lies in the Weil group of `E`

- `relIndex_normal_sup` from `Herbrand.RelativeIndex`: for a normal subgroup `N`, the index of `H` in
  `N ⊔ H` equals the index of `H ∩ N` in `N` (second isomorphism theorem).
- `wildIn_le_of_isOpen_coprime`: an open subgroup `U` of inertia `I_K`, not
  necessarily normal, of index prime to `p`, contains wild inertia. By
  `ker_res_le` (module `Langlands.Correspondence.HenniartWildInertia`), `U`
  contains the kernel of the restriction to the inertia group of some finite
  Galois subextension, so its image `V` there has the same index. The first
  lower group `G₁` is a normal `p`-subgroup (`exists_card_inertiaLowerGroup`),
  so the index of `V ∩ G₁` in `G₁` is a power of `p` (`IsPGroup.index`) that
  divides `[G₁ ⊔ V : V]`, hence the index of `U`; it is therefore one, and
  `G₁ ≤ V`. Since `G₁` is the image of wild inertia (`inertiaLowerGroup_eq_map`)
  and `U` contains the kernel, wild inertia lies in `U`.
- `weilWildInertia_le_range`: if `p` does not divide the degree of `E`, wild
  inertia of the Weil group of `K` lies in the image of `intermediateWeilMap
  K E`. Through `localInertiaEquiv`, the subgroup of inertia fixing `E`
  corresponds to `I ∩ G_E` in absolute inertia `I`, and
  `[I : I ∩ G_E] = [I ⊔ G_E : G_E]` divides `[G_K : G_E] = [E : K]`
  (`IntermediateField.finrank_eq_fixingSubgroup_index`, with `I` normal). So
  the previous lemma applies, and `intermediateWeilMap_range` identifies the
  image with the preimage of `G_E`.

## The two assertions

`tameSubextensionHerbrand` combines this with the module
`Langlands.Correspondence.HenniartTameFieldCount`:

- `TameField.relativeHerbrandPsi_eq` gives `ψ_{E/K}(v) = m v` for `v ≥ 0`. Every
  positive upper group of `K` lies in wild inertia, hence in the Weil group of
  `E`, so the published `relativeHerbrandPsi_sub_eq_of_upperGroup_le` gives
  slope `e_E / e_K = m` on every `[v₀, ∞)` with `v₀ > 0`; continuity at `0`
  and `ψ_{E/K}(0) = 0` conclude.
- For `v > 0`, `TameField.map_mem_upperGroup_iff` gives
  `ι w ∈ W_K^v ↔ w ∈ W_E^{m v}` for the Weil map `ι`, by the published
  `intermediateWeilEquiv_mem_upperGroup_iff` and the first assertion. This
  gives the inclusion of the image in `W_K^v`. Conversely an element of
  `W_K^v` lies in wild inertia (`upperGroup_le_weilWildInertia`), hence in the
  image of `ι`, and its preimage lies in `W_E^{m v}`.

The route follows the provenance of the statement (J.-P. Serre, *Local
Fields* (1979), registered as `serre-1979-local-fields`, IV §2, Corollary 3,
printed pp. 67–68, and IV §3, Remark 2 after the proof of Proposition 14, printed
p. 75):
the first ramification group is a normal `p`-subgroup and therefore fixes a
subextension of degree prime to `p`, which fixes the slope of the Herbrand
function on positive indices.
