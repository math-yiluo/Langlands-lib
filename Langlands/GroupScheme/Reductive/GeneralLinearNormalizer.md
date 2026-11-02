# Points normalizing the diagonal torus of `GL_n` act by permutations

Worker 274.

This is a helper module for the proof of `GeneralLinearRootDatumStatement`. It proves
`weylImage_diagonalTorus n k : weylImage (diagonalTorus n k) =
(permutationAction n k).range` over a field `k` (Milne, Example 21.40, printed
p.436, PDF 452: the permutation matrices represent the cosets of `T(k)` in
`N(k)`, so `W ≅ S_n`). The inclusion `⊇` is
`range_permutationAction_le_weylImage` from `GeneralLinearWeyl`. This module
proves `⊆`.

## The one-variable Laurent test

The test scheme is `Spec k[T, T⁻¹]` over `Spec k`, with the universal unit
`Gm.laurentPoint k` of the module `Langlands.GroupScheme.Torus.Lattice`.
`laurentΓ` is the global-sections isomorphism of `Spec k[T, T⁻¹]`. The module
proves the following lemmas:
- `laurentΓ_zpow` and `laurentΓ_unit`: the universal unit corresponds to `T`.
- `laurentΓ_appTop`: base constants restrict to constant Laurent polynomials,
  by `Scheme.ΓSpecIso_naturality`.
- `laurentΓ_cocharacter`: a cocharacter `ν` of the split torus sends the
  universal unit to the coordinates `T^{mᵢ}`, where
  `m = cocharacterLatticeEquiv ν`.
- `exponent_eq_of_C_mul_T`: `x T^p = T^q x` with `x ≠ 0` in `k` forces `q = p`,
  by injectivity of `AddMonoidAlgebra.single · x`.

## Normalizing points are monomial

Let `n0` normalize the diagonal torus through `σ`, and let `baseMatrix n0 ∈ GL_n(k)`
be its matrix.

- `cocharacter_coord_of_isNormalizingPoint`: if the `(a, b)` entry of `n0` is
  nonzero, then for every `c` the `a`-th coordinate of the cocharacter
  `single c ≫ σ` is `1` if `b = c` and `0` otherwise. The proof restricts the
  normalizing equation to the point `single c (s)` of the diagonal torus over
  `Spec k[T, T⁻¹]`, which gives `n0 diag(1, …, s, …, 1) = diag(s^{m}) n0`. It
  then compares the `(a, b)` entries as Laurent polynomials.
- An invertible matrix over a field has a nonzero entry in each row and each
  column (`exists_ne_zero_row`, `exists_ne_zero_col`). By the previous lemma the
  nonzero entry of each row is unique. Choosing it gives a surjective, hence
  bijective, map `π` on the finite type `n`.
- `exists_perm_of_isNormalizingPoint`: the coordinates of the cocharacters
  `single c ≫ σ` then show that `single c ≫ σ = single (π⁻¹ c)` (by injectivity of
  `cocharacterLatticeEquiv`, with `cocharacterLatticeEquiv_single`). Hence `σ⁻¹`
  agrees with `(torusPerm π⁻¹)⁻¹` on all coordinate cocharacters, and so
  `σ.inv = (torusPerm π⁻¹).inv` (`inv_eq_of_single_comp`, from the decomposition
  `∑ proj c ≫ single c = 𝟙` of the module `Torus.Lattice`).
- `weylImage_le_range_permutationAction`: by `characterAut_torusPerm`, every
  element of the Weyl image is a permutation action.
