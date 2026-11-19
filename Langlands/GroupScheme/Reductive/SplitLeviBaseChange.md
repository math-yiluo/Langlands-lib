# Base change of Levi comparison data to an intermediate field

Author: Worker 5662.

This module proves clause 4 of Task 7605: the comparison of Tits obstructions after a scalar
extension `E/k`, for the base change of the original centralizer and its actual derived
subgroup. Let `k ⊆ E ⊆ K` be a tower of fields with `K/E` Galois. After base change, the
original maximal split torus `S_E` may cease to be maximal, and the derived subgroup
`H_E` may cease to be anisotropic. The module transports Levi comparison data
(`GaloisPinningData.LeviComparison`, module `Reductive/SplitLeviComparison`) along the base
change, and neither property is needed. It then applies the general comparison of module
`Reductive/SplitLeviTitsComparison` over `E`. The transport of Galois pinning data, tori and
characters along `k ⊆ E ⊆ K` is Worker 132's module `Reductive/GaloisPinningBaseChange`
(`GaloisPinningData.baseChange d E`, `weightTransport`, `characterTowerEquiv`,
`torusTowerIso`). Tits uses this comparison over vertex fields (Tits, *Représentations
linéaires irréductibles d'un groupe réductif sur un corps quelconque*, J. reine angew.
Math. 247 (1971), §5.5 and Proposition 5.1).

## The split torus datum

- `SplitTorusDatum.baseChange E s` is the base change of the split torus `S`, of its
  inclusion and torus map, with the base change `cocharacterLattice.baseChange` of its
  cocharacter. Its square is the base change of the square of `s`.
- `SplitTorusDatum.baseChange_restriction`: the restriction to `S_E` of the transport of a
  character `x` of `T_K` is the base change of the restriction of `x` to `S`. The proof uses
  Worker 132's naturality `characterTowerEquiv_comp` and the published tower compatibility
  `StarActionFiniteStage.towerCharacterOf_baseChange` of character base change.
- `SplitTorusDatum.baseChange_restriction_root_eq_zero_iff`: hence a root restricts to zero
  on `S_E` exactly when it restricts to zero on `S`, since character base change is
  injective (published `characterLattice.baseChange_injective`).

## Levi comparison data

- `baseChange_vertexStar`: for `σ ∈ Gal(K/E)`, the star action of the base change on simple
  vertices is the star action of `σ` viewed in `Gal(K/k)`. This is Worker 132's
  `baseChangeRootDatumEquiv_comp_starAction`, read on root indices.
- `mem_baseChange_support`: base change keeps the simple vertices
  (`baseChange_base_support`).
- `LeviComparison.baseChangeVertexEquiv` and `baseChangeVertexEquiv_val`: the vertex
  correspondence after base change. It is the original correspondence `L.vertexEquiv`,
  transported along the two identifications above.
- `LeviComparison.baseChange_root_eq`, `LeviComparison.baseChange_coroot_eq`: the root and
  coroot compatibilities after base change. They follow from those of `L` by naturality of
  the tower isomorphisms (`characterTowerEquiv_comp`, `torusTowerIso_hom_naturality`).
- `LeviComparison.baseChange E L`: Levi comparison data for
  `(GroupScheme.baseChange (algebraBaseMap k E)).map ι` between the base changes of `d` and
  `e`. Its fields come from the corresponding fields of `L`:
  - the kernel torus map and square by functoriality;
  - centralization by `LeviComparison.centralizes_baseChange`;
  - positivity from `L.pos`, `baseChange_restriction` and the published
    `latticePairing_baseChange`;
  - star compatibility from `L.star_eq` at `σ` viewed in `Gal(K/k)`.
- `LeviComparison.baseChange_weightRestriction`: restriction after base change, applied to
  a transported weight, is the transport of the original restriction.

## The comparison over `E`

- `LeviComparison.baseChange_titsObstruction`: for simply connected `G` and `D`, the actual
  Tits obstruction of `G_E` equals that of `D_E` composed with restriction of star-fixed
  weights. Both base changes are simply connected by the published
  `isSimplyConnectedFieldExtension`. The result is
  `titsObstruction_comp_starFixedRestriction` applied to `L.baseChange E`.
- `TitsIndexData.AnisotropicKernelIndex.baseChange_titsObstruction_eq p hG E λ`: the case of
  the Library's actual anisotropic kernel, for every intermediate field `E` of the separable
  closure `K` of `k`. The Lean statement is about such intermediate fields. Every finite
  separable extension of `k` embeds over `k` into `K`, which is how this setting serves
  finite separable extensions; that embedding is not formalized here. The Library's actual
  vertex field `d.starVertexField a` (module `SimplyConnected/TypeD4CubicLeafField`) is such
  an intermediate field, so the theorem applies to it directly. For every weight `λ` of the base change `G_E` fixed by the full star action
  of `Gal(K/E)`, the actual Tits obstruction of `G_E` at `λ` equals the actual Tits
  obstruction of the base change `H_E` of the kernel at the restriction of `λ`. The
  instance that `K/E` is Galois is found automatically. By Worker 132's
  `forall_fixingSubgroup_starAction_iff`, these weights are exactly the transports of the
  original weights fixed by `E.fixingSubgroup`.
- `AnisotropicKernelIndex.baseChange_starFixedRestriction_val`: for a transported weight
  `λ = weightTransport x`, the restricted weight is the transport of the original actual
  restriction `p.comparison.weightRestriction x`.

Every field and every characteristic are allowed. The provenance is internal.
