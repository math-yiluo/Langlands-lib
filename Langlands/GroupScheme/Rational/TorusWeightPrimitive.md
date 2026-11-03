# Primitive weight coordinates on cyclic weight subgroups

Let `σ : TorusAction F I` be a split-torus action on a corepresented group functor
`F` with representing algebra `B` (`e : (F ⋙ forget GrpCat).CorepresentableBy B`,
`Rational.TorusGrading`), let `a ≠ 0` be a character and `r > 0`, and let `U_r` be the
weight subgroup of the cyclic tail `cyclicTail a r` (`Rational.TorusWeightSubgroups`,
`Rational.TorusWeightPolynomial`). This module shows that on `U_r` the coordinates of
weight components of weight `r • a` are additive (primitive), that they cut out
`U_{r+1}` inside `U_r`, and, over a field, that the coordinate algebra of `U_r` is a
polynomial algebra in such primitive coordinates and further coordinates. All
declarations are in namespace `Langlands.GroupScheme.Corepresented`.

## Statements

Dual numbers, for an `R`-algebra `A`:

- `snd_coord_mul`: if two points `z`, `z'` of `F` over `A[ε] = DualNumber A` both map to
  the identity over `A` (under `TrivSqZeroExt.fstHom`), then for every `f : B` the
  `ε`-part of `coord e (z * z') f` is the sum of the `ε`-parts of `coord e z f` and
  `coord e z' f`.

Supported elements:

- `coeff_mul_of_supported`: for `x`, `y` supported on `{0} ∪ P`, if `χ ≠ 0` and `χ` is
  not a sum of two elements of `P`, then `(x * y)_χ = x_0 y_χ + x_χ y_0`.
- `dualCoeffHom A P h0 hχ0 hχ`, for `0 ∉ P` and such `χ`, is the `R`-algebra map from
  the subalgebra of `A[I → ℤ]` of elements supported on `{0} ∪ P` to `A[ε]` sending `s`
  to `s_0 + s_χ ε` (`dualCoeffHom_apply`). Multiplicativity is
  `coeff_zero_mul_of_supported` and `coeff_mul_of_supported`.
- `map_subalgebraHom_injective`: points of `F` over a subalgebra are determined by their
  images over the ambient algebra.

Weight subgroups, for a subsemigroup `P`:

- `supportedPointFun` and `supportedPoint e σ P : U_P(A) →* F(S)`, where `S` is the
  subalgebra of `A[I → ℤ]` of elements supported on `{0} ∪ P`: the twisted point
  `hat σ x` of `x ∈ U_P(A)` has coordinates in `S`, and `supportedPoint` is the
  corresponding point over `S` (`map_supportedPointFun`, `coord_supportedPoint`). It is
  a group homomorphism because `hat σ` is and points over `S` are determined by their
  images.
- `coord_mul_comp_of_notMem_add`: if `0 ∉ P`, `χ ≠ 0` and `χ` is not a sum of two
  elements of `P`, then for `x, y ∈ U_P(A)` and `f : B`,
  `coord e (x * y) (comp e σ χ f) = coord e x (comp e σ χ f) + coord e y (comp e σ χ f)`.

Cyclic tails, for `a ≠ 0` and `r > 0`:

- `nsmul_ne_zero_of_pos` (`r • a ≠ 0`) and `add_ne_nsmul_of_mem_cyclicTail` (`r • a` is
  not a sum of two elements of `cyclicTail a r`).
- `coord_mul_comp_nsmul`: on `U_r`, the coordinates of weight components of weight
  `r • a` are additive.
- `mem_weightSubgroup_succ_iff`: for `x ∈ U_r(A)`, `x ∈ U_{r+1}(A)` iff
  `coord e x (comp e σ (r • a) f) = 0` for all `f`.

Over a field `k`, with `B` formally smooth and of finite type:

- `exists_eq_mk_comp`: a homogeneous element of weight `m` of `B ⧸ weightIdeal e σ P` is
  the image of a weight component `comp e σ m f`.
- `exists_primitive_coordinates`: there are `N`, elements
  `y : Fin N → B ⧸ weightIdeal e σ (cyclicTail a r)`, a finite type `ι : Type` and
  `z : ι → B ⧸ weightIdeal e σ (cyclicTail a r)` such that
  1. each `y i` is homogeneous of weight `r • a` for the restricted action;
  2. the `y i` are primitive: for points `x`, `x'` of `U_r` over any `k`-algebra,
     `coord (x * x') (y i) = coord x (y i) + coord x' (y i)`, coordinates taken for the
     corepresentation `weightCorep` by `B ⧸ weightIdeal e σ (cyclicTail a r)`;
  3. a point `x` of `U_r` lies in `U_{r+1}` iff `coord x (y i) = 0` for all `i`;
  4. `MvPolynomial.aeval (Sum.elim y z) : k[Fin N ⊕ ι] → B ⧸ weightIdeal e σ (cyclicTail a r)`
     is bijective.

## Proofs

`snd_coord_mul` uses two independent infinitesimals, as in the Library's
`Lie.kernelDerivationEquiv_mul`. Let `w` be the product of the images of `z` and `z'`
over `A ⊕ (A × A)ε` under `ε ↦ (ε, 0)` and `ε ↦ (0, ε)` (`Lie.squareMap` of `inl`,
`inr`). Mapping `w` along the projections and along the sum `A × A → A` gives `z`, `z'`
and `z * z'`, because the composite maps are the identity or factor through the
reduction to `A`, which sends `z`, `z'` to the identity. Comparing the `ε`-parts of the
coordinates gives the formula.

For `coord_mul_comp_of_notMem_add`, compose `supportedPoint` with `F.map` of
`dualCoeffHom` to get a homomorphism `ζ : U_P(A) → F(A[ε])`. By `coord_hat_coeff`,
`coord e (ζ x) f = coord e x (comp e σ 0 f) + coord e x (comp e σ χ f) ε`. Since `0 ∉ P`,
the constant part is `AffineLinearEmbedding.counit e f` (`counit_comp`), so `ζ x` reduces to the identity
(`eq_one_iff`), and `snd_coord_mul` applied to `ζ (x * y) = ζ x * ζ y` gives additivity.
For cyclic tails, `n • a + n' • a = r • a` with `n, n' ≥ r > 0` is impossible because
`n ↦ n • a` is injective.

`mem_weightSubgroup_succ_iff`: `cyclicTail a r` and `cyclicTail a (r + 1)` differ only in
`r • a`, and the counit of a weight component of nonzero weight is zero.

`exists_primitive_coordinates`: take the polynomial coordinates `x` and degrees `d ≥ r`
of `exists_aeval_bijective_cyclicTail`. Let `y` be the `x i` with `d i = r`, reindexed by
`Fin N` with `Fintype.equivFin`, and `z` the `x i` with `d i ≠ r`. Then `Sum.elim y z` is
`x` composed with an equivalence `Fin N ⊕ ι ≃ Fin n`, so its evaluation is bijective
(`MvPolynomial.renameEquiv`). Primitivity of `y i` follows from `exists_eq_mk_comp`,
`coord_cut_mk` and `coord_mul_comp_nsmul`. For the kernel: if `x ∈ U_{r+1}`, its
coordinates kill every `comp e σ (r • a) f` (`mem_weightSubgroup_succ_iff`), in
particular the `y i`. Conversely, the image of `comp e σ (r • a) f` in the quotient is
homogeneous of weight `r • a` (`comp_restrict`, `isHomogeneous_comp`), so it is a
`k`-linear combination of the `y i` by `mem_span_of_mem_graded` (for the `ℕ`-grading
`n ↦ n • a`). So if `coord x` kills the `y i`, it kills it, and
`mem_weightSubgroup_succ_iff` gives `x ∈ U_{r+1}`.

## Provenance

Internal supporting material for the proof of
`Langlands.GroupScheme.RelativeRoot.CyclicWeightFiltrationStatement` (task 023326af).
Conrad–Gabber–Prasad, *Pseudo-reductive groups*, 2nd ed., Lemma 3.3.8 and its proof
(printed pp.111-112), show that `U_{A_j}(G)/U_{A_{j+1}}(G)` is a vector group whose Lie
algebra has the single weight `j • a`. Here the corresponding quotient map is to be
given explicitly by the primitive coordinates `y` of weight `r • a`; this module
provides those coordinates. The route is internal to this formalization.
