# The closed subgroup `T ⋉ U_{Φ⁺}` over an affine base

This module proves clause 2 of
[`AffineSplitRootSubgroupSpanningStatement`](AffineSplitRootSubgroupSpanningStatement.md), the
last assertion of Conrad, *Reductive group schemes* (2014), Theorem 5.1.13, p.143: the map
`T × U_{Φ⁺} → G` is an isomorphism onto a closed subgroup. It adds theorems only: no
definitions, statements or axioms. Everything is in `Langlands.GroupScheme.LocalSplitCell`,
with the binders of the target statement (`R` any commutative ring, `G` reductive and
affine over `Spec R`, `i` a closed fibrewise-maximal split torus with fibrewise root datum
`P`, `u` root parametrizations).

## Results

- `orderedProduct_fin_zero`: the ordered product over the empty enumeration is `1`.
- `cellMap_zero_mono neg pos`: suppose the big-cell map `cellMap i u neg pos` is an open
  immersion. Then the torus-times-positive map `cellMap i u Fin.elim0 pos`,
  `(t, w) ↦ i(t) ∏ₖ u_{pos k}(wₖ)`, is a monomorphism. A point `(t, w)` of
  `cellObj R I 0 n` is sent to the point `(0, t, w)` of `cellObj R I m n`, which has the
  same image in `G`. Two points with equal images therefore have equal images under the
  monomorphism `cellMap i u neg pos`, so their torus and positive coordinates agree.
- `exists_closedSubgroup_torus_positive` (clause 2): for a base `b` and an enumeration
  `pos` of the `b`-positive roots, there are a group scheme `B`, a closed subgroup
  `jB : B ⟶ G` and an isomorphism `φ : cellObj R I 0 n ≅ B.X` with
  `φ ≫ jB = cellMap i u Fin.elim0 pos`.

## Proof of clause 2

1. Choose any enumeration `neg` of the negative roots. The Library's
   `LocalSplitBigCell.isOpenImmersion_cellMap` shows that the big-cell map is an open
   immersion, so the map `c := cellMap i u Fin.elim0 pos` is a monomorphism.
2. `exists_coPairing_eq_height` gives `d > 0` and a cocharacter `ν` with
   `⟨α, ν⟩ = d · height_b(α)`. So `ν` is negative on the negative roots, positive on the
   positive roots, and nonzero on every root. Let `χ = AffineRegularBorel.cocharacter i ν`.
   For this regular `χ`, `AffineRegularBorel.centralizer_eq_range` identifies the dynamic
   centralizer `Z_G(χ)` with the image of the torus.
3. `B` is the Library's closed representative of the dynamic parabolic `P_G(χ)`, namely
   `Dynamic.Affine.parabolicScheme χ` with inclusion `parabolicHom χ`.
4. The map `c` lands in `P_G(χ)`. The torus factor lies in `Z_G(χ) ⊆ P_G(χ)`. The positive
   product lies in `U_G(χ) ⊆ P_G(χ)` by `orderedProduct_mem_unipotent`. So `c` factors as
   `f ≫ jB`.
5. Conversely, take the universal point `jB` of `P_G(χ)`, with limit `l` at `0`
   (`Dynamic.exists_hasLimit`). Then `l` lies in the centralizer, hence `l = t ≫ i` for a
   torus point `t`, and `l⁻¹ · jB` lies in `U_G(χ)`. `B` is affine, so the Library's
   `exists_orderedProduct_eq_of_mem_unipotent_of_affine` writes `l⁻¹ · jB` as an ordered
   positive product with coordinates `c'`. The point `ψ := (t, c')` of `cellObj R I 0 n`
   then satisfies `ψ ≫ c = jB`.
6. `f` and `ψ` are mutually inverse, since `c` and `jB` are monomorphisms.
