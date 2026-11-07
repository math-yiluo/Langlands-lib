# Permutation conjugation of block unipotent subgroups of `GL_n`

This internal module shows that renumbering the indices of a weight by a
permutation `τ` corresponds to conjugating block unipotent subgroups of `GL_n`
by the permutation matrix of `τ`. It also shows that every threshold weight on
`Fin m` can be renumbered into the standard two-block weight
`Langlands.GeneralLinear.twoBlockWeight`. Here `blockUnipotentSubgroup A v` is
the existing subgroup of invertible matrices `g` with `g i j = δ i j` whenever
`v i ≤ v j`. `blockUnipotent n R v` is the corresponding subgroup functor of
`groupScheme n R`.

## Matrices

The module reuses the published permutation matrices of
`Langlands.GroupScheme.Reductive.GeneralLinearWeyl`: for a permutation `w` of a
finite index type `n`, `permMatrix A w` has `(a, b)` entry one exactly when
`a = w b`, and `permGL A w` is it as an element of `GL n A`.

- `permMatrix_eq_toMatrix`: `permMatrix A w` equals the partial-equivalence
  matrix `w.symm.toPEquiv.toMatrix`.
- `permGL_symm_conj_apply`: for `P = permGL A τ.symm`, the matrix `P * g * P⁻¹`
  has `(i, j)` entry `g (τ i) (τ j)`. The proof rewrites both factors with
  `permMatrix_eq_toMatrix` and uses Mathlib's row and column permutation lemmas
  for partial-equivalence matrices.
- `permGL_symm_conj_mem_blockUnipotentSubgroup_iff`: if `w (τ k) = v k` for all
  `k`, then `P * g * P⁻¹` lies in `blockUnipotentSubgroup A v` iff `g` lies in
  `blockUnipotentSubgroup A w`. The proof combines `permGL_symm_conj_apply`
  with the injectivity of `τ`, which preserves the identity matrix entries.

## Subgroup functors

`blockUnipotent_eq_comap_innerIso_permPoint`: if `w (τ k) = v k` for all
`k`, then `blockUnipotent n R w` is the inverse image of
`blockUnipotent n R v` under the inner automorphism
`(groupScheme n R).innerIso (permPoint R τ.symm)`. Here `permPoint` is the
published base point with matrix `permGL`. Pointwise, the inner automorphism is
conjugation by the constant point (`comp_innerIso_hom`), whose matrix is
`permGL _ τ.symm` by the published `pointsEquiv_constantPoint_permPoint`. The
statement then reduces to `permGL_symm_conj_mem_blockUnipotentSubgroup_iff`.

## Threshold weights

`thresholdWeight e c k` is `1` when `c < e k` and `0` otherwise.
`thresholdWeight_le_of_le` states that it is weakly increasing in `e`: if
`e i ≤ e j`, then `thresholdWeight e c i ≤ thresholdWeight e c j`.

`exists_perm_thresholdWeight_eq_twoBlockWeight`: for every `e : Fin m → ℤ` and
`c : ℤ`, there are natural numbers `a`, `b`, a proof `h : a + b = m` and a
permutation `τ` of `Fin m` such that:

- `0 < a` iff some `e k` exceeds `c`;
- `0 < b` iff some `e k` is at most `c`;
- `thresholdWeight e c (τ k) = twoBlockWeight h k` for every `k`.

Here `a` and `b` are the numbers of indices with `c < e k` and with
`e k ≤ c`. The permutation `τ` lists the first kind of index, then the second,
through `Equiv.sumCompl` and `finSumFinEquiv`.

## Provenance

The module is internal. Its content is elementary permutation matrix algebra
with the published block subgroups, point equivalences and inner
automorphisms. No literature theorem is invoked. The module makes no claim
about measures, quotients or rational parabolic subgroups.
