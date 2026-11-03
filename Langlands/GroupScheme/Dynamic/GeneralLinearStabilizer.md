# Closed subgroups of `GL_n` and the opposite cell

This internal unit contains the algebraic heart of the opposite-cell proof, phrased purely in
terms of polynomial ideals. Let `k` be a field, `n` a finite index type and `e : n → ℤ` a weight
vector. Let `J` be an ideal of the polynomial ring `k[x_{ij}, y_{ij}]` of the coordinates of
`GL_n`, as in `GeneralLinearTranslation`. For a `k`-algebra `S`, `zeroLocus S J` is the set of
`g : GL n S` at which every polynomial of `J` vanishes, after evaluating `x_{ij}` at `g_{ij}`
and `y_{ij}` at `(g⁻¹)_{ij}`.

The main theorem `mem_zeroLocus_of_mul_mem` has four hypotheses:

* `ideal n k ≤ J`: `J` contains the ideal of `GL_n` (the relations `x y = 1` and `y x = 1`);
* `ZeroLocusMulClosed J`: for every `k`-algebra `R` in the universe of `k`, `zeroLocus R J` is
  closed under multiplication;
* `1 ∈ zeroLocus k J`;
* `diag(T ^ e i) ∈ zeroLocus k[T, T⁻¹] J`, where `T` is the unit `unitT k` of the Laurent
  polynomials.

Let `v q ∈ zeroLocus S J` for a `k`-algebra `S`, with `v` in `blockUnipotentSubgroup S (-e)`
and `q` in `blockParabolicSubgroup S e`. The theorem concludes that `q ∈ zeroLocus S J`.

## Pivot coordinates

Let `K` be a field, `ι` a finite index type and `a : ι → ℤ` weights. `coordinateSubspace K s`
is the space `C(s)` of vectors vanishing outside the finite set `s`. `weightPart a w c` is the
weight-`w` component of `c`.

`exists_pivot` takes a subspace `W` that contains the weight components of its vectors. It
produces a set `s` and a matrix `N` with four properties:

1. the entries of `N` go only from columns outside `s` to rows in `s`;
2. `N` has no entries between different weights;
3. for `j ∉ s`, column `j` of `1 + N` lies in `W`;
4. `((1 - N) c)_i = 0` for every `c ∈ W` and `i ∈ s`.

The proof takes `s` of maximal cardinality with `W ⊓ C(s) = ⊥`. Each basis vector `e_j` with
`j ∉ s` is then `w_j + c_j` with `w_j ∈ W` and `c_j ∈ C(s)`. Maximality yields a nonzero
`v ∈ W ⊓ C(s ∪ {j})`, whose `j` entry is nonzero, and `w_j` is a rescaling of `v`.

The vector `w_j` is homogeneous of the weight of `j`. Indeed, `w_j` minus its weight-`a j`
component lies in `W`. It also lies in `C(s)`, because it equals the weight-`a j` component of
`c_j` minus `c_j`. So it vanishes. Column `j` of `N` is `w_j - e_j`. Finally, for `c ∈ W` the
vector `c - ∑_{j ∉ s} c_j w_j` lies in `W ⊓ C(s) = ⊥`, which gives property 4.

`linearMap_apply_eq_sum` expands a linear functional in the standard basis.

## Coefficient vectors

`ofCoeffs d` is the `S`-linear map that sends a coefficient vector over `Exponent n d` to the
polynomial with those coefficients. `coeff_ofCoeffs`, `ofCoeffs_coeff` and `ofCoeffs_single`
show that it is inverse to taking coefficients in degree at most `d`. `totalDegree_ofCoeffs_le`
and `map_ofCoeffs` give its degree bound and its compatibility with coefficient maps.
`totalDegree_translate_le` states that right translation preserves the bound `deg ≤ d`.

`values_map` and `map_mem_zeroLocus` state that a `k`-algebra map `S → S'` carries zeros of `J`
over `S` to zeros over `S'`.

## Functionals vanishing on `J`

* `exists_functional_extension`: let `μ` be a functional on the coefficient vectors of degree at
  most `d` that kills the coefficient vectors of polynomials of `J`. Then `μ` is the restriction
  of a functional `ℓ` on all of `k[x, y]` that kills `J`. The proof is linear algebra over `k`.
  The map from coefficient vectors to `k[x, y] / J` factors injectively through a quotient on
  which `μ` is defined, and an injective linear map has a left inverse.
* `baseChangeFunctional S ℓ` is the `S`-linear extension of `ℓ` to `S[x, y]` in the monomial
  basis. `baseChangeFunctional_eq_zero` states that it kills the extension of `J` to `S`. The
  set of `F` with `ℓ_S(G F) = 0` for all `G` is an ideal, and it contains the image of `J`,
  because `ℓ_S(X^m f) = ℓ(X^m f)` and `ℓ` kills `J`.
* `sum_coeff_mul_eq_zero` combines the two. For such a `μ` and for `F` in the extension of `J`
  to `S` with `deg F ≤ d`, the sum `∑_m F_m μ(e_m)` vanishes in `S`.

## Translation and grading

Let `coeffSubspace J d` be the space `W_d` of coefficient vectors of polynomials of `J` of
degree at most `d`.

* `ideal_le_map`: the ideal of `GL_n` over `S` lies in the extension of `J` to `S`.
* `translate_map_mem`: let `h ∈ zeroLocus S J`. Then right translation by `h` maps the image in
  `S[x, y]` of each `f ∈ J` into the extension `J_S` of `J` to `S`. The proof uses the generic
  point `x` of `GL_n` over `R = S[x, y] / J_S`, which exists by `ideal_le_map` and lies in
  `zeroLocus R J`. The image of `h` in `GL n R` is also a zero, so `x h` is a zero by
  multiplicativity. Hence `f(x h) = 0` in `R`, and `f(x h)` is the class of
  `translate h f_S` (`aeval_values_translate`).
* `unitT k` is the unit `T` of `k[T, T⁻¹]`, and `coe_unitT_zpow` identifies its powers with the
  monomials `T^j`.
* `weightPart_mem_coeffSubspace` states that `W_d` is graded for the monomial weights. Suppose
  some weight component of `c ∈ W_d` lies outside `W_d`. Then a functional `μ` kills `W_d`
  but not that component. Translating `ofCoeffs d c` by `diag(T ^ e i)` gives
  `∑_m c_m T^{weight m} X^m` (`translate_diagonalUnits_monomial`). This lies in the extension
  of `J` to `k[T, T⁻¹]` by `translate_map_mem`. Then `sum_coeff_mul_eq_zero` gives
  `∑_m c_m μ(e_m) T^{weight m} = 0`. Its coefficient of `T^w` is `μ` of the weight-`w`
  component, a contradiction.

## The stabilizer argument

Proof of `mem_zeroLocus_of_mul_mem`. Let `g ∈ J` and choose `d ≥ deg g`.

1. Apply `exists_pivot` to the graded space `W_d` with the monomial weights. Since `N² = 0`,
   `B = 1 + N` is invertible with inverse `1 - N`. It is block Levi for the monomial weights.
   Let `B_S` be its image over `S`.
2. Let `ρ = translationHom S d`, and set `Q = B_S⁻¹ ρ(q) B_S` and `V = B_S⁻¹ ρ(v) B_S`. By
   `GeneralLinearTranslation` and the Levi normalization of `GeneralLinearCellBlock`, `Q` is
   block parabolic for the monomial weights, and `V` is block unipotent for their negatives.
3. Let `r ∈ s` and `j ∉ s`. The entry `(r, j)` of `B_S⁻¹ ρ(v q) B_S` vanishes. Column `j` of
   `B` is the coefficient vector of some `f_j ∈ J`. By `translate_map_mem` (with `h = v q`),
   the translate of `f_j` by `v q` lies in the extension of `J` to `S`. Apply
   `sum_coeff_mul_eq_zero` to the functional `c ↦ ((1 - N) c)_r`, which kills `W_d` by pivot
   property 4. The resulting sum is exactly that entry.
4. Since `B_S⁻¹ ρ(v q) B_S = V Q`, the block lemma `eq_zero_of_eq_mul_of_compl_zero` (with
   `I` the complement of `s`) gives `Q_{rj} = 0` for `r ∈ s` and `j ∉ s`.
5. Evaluate `g` at `q`. By `aeval_values_translate`, `g(q)` is the value at the identity of the
   translate of `g` by `q`. Write `ℓ_m` for the value of `X^m` at `1` and `c_g` for the
   coefficient vector of `g`. Then `g(q) = (ℓ B_S) · Q · (B_S⁻¹ c_g)`.
   * For `j ∈ s`, `(B_S⁻¹ c_g)_j = ((1 - N) c_g)_j = 0`, since `c_g ∈ W_d`.
   * For `j ∉ s`, `(ℓ B_S)_j` is the value of `f_j` at `1`. It vanishes because
     `1 ∈ zeroLocus S J`, which is the image of the hypothesis over `k`.
   * The remaining terms involve `Q_{rj}` with `r ∈ s` and `j ∉ s`, which vanish by step 4.

   Hence `g(q) = 0`.

## Provenance

This is a variant of Step 3 of the proof of Proposition 2.1.8(3) in Conrad–Gabber–Prasad,
*Pseudo-reductive groups* (2nd edition). There, the subgroup is the stabilizer of a line in a
representation of the ambient group, and a factor of a product in the open cell of the ambient
group is shown to stabilize the line. Here, the line is replaced by the subspace `W_d` of the
representation on polynomials of degree at most `d`, after a unipotent block Levi change of
basis to the coordinate subspace of pivot columns. The role of the line-stabilizer computation
is taken by the block lemma, and the grading of `W_d` comes from the diagonal cocharacter. The
reduction to ideals and zero loci, and all intermediate statements, are internal to this
development.

The unchanged `GeneralLinear.weightPart` and `weightPart_add` declarations
are imported from `Dynamic/GeneralLinearWeightComponents`, shared with the
flag-limit construction.
