# Hyperbolic bases of antihermitian forms of Witt index one

Module `Langlands.GroupScheme.Quaternionic.HyperbolicBasis`.

Setting: `K` a field, `D` a division `K`-algebra, `σ : FirstKindInvolution K D`, and
`h(x, y) = ∑ i j, x i H i j σ(y j)` the form `σ.sesqForm H` on row vectors (published in
`Quaternionic.Forms`). "Nondegenerate" means `IsUnit H`; "antihermitian" is the published
`σ.IsAntihermitian H` (`ᵗH^σ = -H` and every diagonal entry lies in `{a - σ a}`).

## Results

- Private semilinearity lemmas: `h` is additive in both arguments,
  `h(a x, y) = a h(x, y)` and `h(x, b y) = h(x, y) σ(b)`.
- `sesqForm_eq_sum_vecMul`: `h(x, y) = ∑ j, (x H) j σ(y j)`.
- `mul_mul_matrix_apply`: `(P H ᵗP^σ) i j = h(P i, P j)`, the Gram matrix of the rows of `P`.
- `IsAntihermitian.sesqForm_swap`: `h(y, x) = -σ(h(x, y))`.
- `exists_eq_sub_matrix` (for a linearly ordered index type): an antihermitian `H` is
  `A - ᵗA^σ`, with `A` the strictly upper part of `H` plus diagonal entries `a i` such that
  `H i i = a i - σ(a i)`.
- `sesqForm_self_mem_alternatingSubspace`: consequently `h(x, x) = h_A(x, x) - σ(h_A(x, x))`
  lies in `{a - σ a}` for every `x` (the form is trace-valued), in every characteristic.
- `exists_sesqForm_ne_zero`: for invertible `H` and `x ≠ 0` some `y` has `h(x, y) ≠ 0`
  (take `y` a standard basis vector at a nonzero entry of `x H`).
- `bddAbove_isotropic_finrank`, and the imported `finrank_le_wittIndex`: dimensions of totally
  isotropic subspaces are bounded by `card n` and by the Witt index.
- `exists_isotropic_of_wittIndex_eq_one`: Witt index `1` gives a nonzero isotropic `e`
  (the supremum `1` is attained, so a totally isotropic line exists).
- `exists_hyperbolic_pair`: for `H` invertible antihermitian and isotropic `e ≠ 0` there is
  `f` with `h(e, f) = 1`, `h(f, f) = 0`. Proof: scale a `y` with `h(e, y) ≠ 0` to get
  `h(e, y') = 1`, write `h(y', y') = t - σ t` and put `f = y' - t e`.
- `isUnit_of_mul_mul_matrix_eq`: if `P H ᵗP^σ = G` with `G` invertible then `P` is invertible
  (`P` has the right inverse `H ᵗP^σ G⁻¹`).
- **`exists_gramTwo`**: for `H ∈ M_2(D)` antihermitian, invertible, of Witt index `1`, there is
  an invertible `P` with `P H ᵗP^σ = gramTwo D = !![0, 1; -1, 0]` (rows `e, f`).
- **`exists_gramThree`**: for `H ∈ M_3(D)` antihermitian, invertible, of Witt index `1`, there
  are an invertible `P` and `c ∈ {a - σ a}`, `c ≠ 0`, with
  `P H ᵗP^σ = gramThree c = !![0, 1, 0; -1, 0, 0; 0, 0, c]`. The third row `w ≠ 0` lies in
  the kernel of `x ↦ (h(x, e), h(x, f))` (rank–nullity, `D^3 → D^2`) and `c = h(w, w)`. If
  `c = 0`, then `e, w` are linearly independent (pair with `f`) and span a totally isotropic
  plane, contradicting Witt index `1`.

## Provenance

Internal. Every step is proved directly from the published definitions of
`Quaternionic.Forms` (`sesqForm`, `IsAntihermitian`, `wittIndex`), rank–nullity, and
finite-dimensional linear algebra over the division ring `D`. This is the familiar construction
of a hyperbolic pair and its orthogonal complement, specialised to Witt index one and ranks two
and three. The trace-valued condition makes the hyperbolic partner isotropic in every
characteristic.

The four semilinearity identities, the antihermitian swap identity and
`finrank_le_wittIndex` are reused from [FormLemmas](FormLemmas.md).
