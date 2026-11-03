# The image lattice of a homomorphism from a lattice torus

Author: Worker 1178.

This internal module factors a homomorphism from a lattice torus through the
lattice torus of its image lattice.

For `α : latticeFunctor R Λ ⟶ F'` classified by `ψ : B' → R[Λ]`,
`imageSubgroup d α` is the set of `m` with `[m]` in the range of `ψ`. It is an
additive subgroup: `[0] = 1`, `[a + b] = [a][b]`, and `[−m]` is the antipode
of `[m]`, which stays in the range by `classify_antipode`.

Over a field `k`:

- `mem_imageSubgroup_of_coeff_ne_zero` and `mem_range_iff`: an element of
  `k[Λ]` lies in the range of `ψ` exactly when its support lies in the image
  lattice `M`. The forward direction divides the coefficient identity of
  `LatticeImage` by a nonzero coefficient; the converse writes the element as
  a combination of the `[m]`.
- `incl M = lmap M.subtype : k[M] → k[Λ]` is `mapDomain` of the inclusion,
  hence injective, and `range_incl` identifies its range with that of `ψ`.
- `imageClassify d α : B' → k[M]` is `ψ` corestricted to that range and
  transported along `incl`; `imageClassify_comp_incl` and
  `imageClassify_surjective` hold.
- `imageClassify_comul`: the comultiplication compatibility of
  `imageClassify` follows from that of `ψ` after composing with
  `incl ⊗ incl`, which is injective because tensor products of injective maps
  of vector spaces are injective (`TensorProduct.map_injective_of_flat_flat`).
- `imageHom d α := ofClassify … (imageClassify d α)` is the resulting natural
  homomorphism from the lattice torus of `M`; `latticeMap_comp_imageHom`
  proves `latticeMap M.subtype ≫ imageHom d α = α` by comparing classifying
  maps.
- `IsCentralNat.imageHom`: the universal central identity for
  `imageClassify` follows from that of `ψ` after composing with the injective
  map `incl ⊗ id : k[M] ⊗ B' → k[Λ] ⊗ B'` (flatness over a field).

## Provenance

Internal. This is the image of a homomorphism of a split torus into an affine
group, as a closed subgroup that is again a split torus, formulated on
coordinate algebras.
