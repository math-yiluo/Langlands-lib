# Graded polynomial coordinates on the first cyclic weight subgroup

Author: Worker 1423.

Helper module for the proof of
`Langlands.Aubert.General.RationalPointFamily.DynamicUnipotentVectorFiltrationStatement`.
All declarations are in namespace `Langlands.GroupScheme.Corepresented`.

Throughout, `σ` is a split-torus action on a corepresented group functor `F` with coordinate
algebra `B`, `a ≠ 0` is an exponent vector, and `U_r` is the weight subgroup
`weightSubgroup e σ (cyclicTail a r)`. The Library's `exists_aeval_bijective_cyclicTail`
(`Rational.TorusWeightPolynomial`), applied with `r = 1`, gives elements
`x : Fin n → B ⧸ weightIdeal e σ (cyclicTail a 1)`, homogeneous of weights `d i • a` with
`d i > 0`, such that `aeval x` is bijective. These are graded polynomial coordinates on `U_1`.
The lemmas below take such `x` (and only the surjectivity of `aeval x` where enough).

## Polynomial lemmas

- `aeval_weightedHomogeneousComponent_eq_zero`: a weighted homogeneous component of degree
  `j`, `0 < j < r`, vanishes at a point whose coordinates of weight less than `r` vanish.
  Every monomial of weight `j` contains a variable of weight at most `j`.
- `aeval_eq_sum_of_isWeightedHomogeneous`: a weighted homogeneous polynomial of degree
  `r > 0`, with positive weights, evaluated at such a point, is
  `∑_{d j = r} coeff (single j 1) p * v j`. A monomial of weight `r` either contains a variable
  of smaller weight or is a single variable of weight `r`
  (`GradedFormallySmooth.eq_single_of_weight_le`).

## Coordinates on the first cyclic weight subgroup

- `comp_cyclicTail_mem_range`: all weights on the coordinate algebra of `U_r` are multiples of
  `a`. This is the support condition needed for the Library's `ℕ`-graded algebra structure
  `gradedAlgebra … (multiplesHom (I → ℤ) a)`.
- `mem_weightSubgroup_iff_coord_eq_zero`: a point `u` of `U_1` lies in `U_r` exactly when
  `coord u (x i) = 0` for all `i` with `d i < r`. One direction writes `x i` as the image of a
  weight component (`exists_eq_mk_comp`). For the other, a weight component of weight
  `j • a`, `1 ≤ j < r`, is the image of a weighted homogeneous polynomial of degree `j` in
  `x`. This uses the Library's `GradedFormallySmooth.decompose_aeval` and
  `DirectSum.decompose_of_mem_same`, and the polynomial vanishes at `u`.
- `coord_mul_of_weight_eq`: on `U_r` the coordinates `x i` with `d i = r` are additive (the
  Library's `coord_mul_comp_nsmul`).
- `coord_eq_of_apply_eq`, `exists_coord_eq`: points of a corepresented functor whose
  coordinate algebra is generated, respectively freely generated, by `x` are determined by,
  respectively exist for any prescribed, values on `x`.
- `coord_one_of_isHomogeneous`: homogeneous coordinates of positive weight vanish at the
  identity.
- `eq_one_of_mem_weightSubgroup_of_lt`: if `d i < r` for all `i`, then `U_1 ∩ U_r` is trivial.

## Provenance

Internal. The statement that the coordinate algebra of `U_A(G)` for a cyclic `A` is a graded
polynomial algebra is the Library's formalization of Conrad–Gabber–Prasad, *Pseudo-reductive
groups*, 2nd ed., Lemma 3.3.8; the lemmas here only manipulate those coordinates.
