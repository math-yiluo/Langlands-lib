# Intertwiners into two-factor external tensors

Lean module: `Langlands.Representation.Classification.LeftCuspidalDerivative.Criterion`.

These are internal helper results for the proof of
`Langlands.Classification.LeftCuspidalDerivative.LeftCuspidalDerivativeLemma`, used by the
first-block criterion (`LeftCuspidalDerivative/FirstBlock.lean`). They do not follow a
specific source. Everything here is generic over a pair of groups `H : Fin 2 → Type`, a
representation `W` of `H 0 × H 1` (as `∀ i, H i`), and coefficient representations
`τ i` of `H i`. `W|_{H 0}` denotes `W.comp (MonoidHom.mulSingle H 0)`.

## Tensor evaluation (section `TensorEvaluation`)

* `exists_dual_lid_rTensor_ne_zero`: a nonzero `w ∈ A ⊗ S` has nonzero contraction against
  some functional on `A` (expand in a basis of `A`).
* `tensorEval e : A ⊗ S → (X → A)`, `a ⊗ s ↦ (x ↦ e s x • a)`, for a linear map
  `e : S → (X → ℂ)`; `tensorEval_tmul`, `tensorEval_dual` (contracting the values with a
  functional `φ` on `A` gives `e` of the contracted tensor).
* `tensorEval_injective`: `tensorEval e` is injective when `e` is (combine
  `tensorEval_dual` with `exists_dual_lid_rTensor_ne_zero`).

## Two factors (section `FinTwo`)

* `finTwoTensorEquiv`: the indexed tensor product over `Fin 2` is `V 0 ⊗ V 1`
  (`finTwoTensorEquiv_tprod`).
* `finTwoFunAction τ m F = (g ↦ τ (m 0) (F (g * m 1)))`: the action of `H 0 × H 1` on
  functions `H 1 → V 0`.
* `finTwoEval e`: the composite of `finTwoTensorEquiv` and `tensorEval e`;
  `finTwoEval_injective` for injective `e`; `finTwoEval_external`: if `e` turns the action
  of `τ 1` into right translation, then `finTwoEval e` intertwines the external tensor
  `FiniteTensor.external τ` with `finTwoFunAction (τ 0)`.

## The key construction (section `Key`)

* `translateEval W τ₀ φ w = (g ↦ φ (W (mulSingle 1 g) w))` for a first-factor intertwiner
  `φ : W|_{H 0} → τ₀`; `translateEval_equivariant`: it turns `W` into `finTwoFunAction τ₀`.
* `exists_external_ne_zero`: if `φ ≠ 0`, `e` is injective and turns `τ 1` into right
  translation, and every `translateEval W (τ 0) φ w` lies in the range of `finTwoEval e`,
  then there is a nonzero intertwiner `W → τ 0 ⊠ τ 1`. Proof: factor `translateEval`
  through the injective `finTwoEval e` (`LinearEquiv.ofInjective`); equivariance follows
  from `finTwoEval_external` and `translateEval_equivariant`; nonvanishing by evaluating
  at `g = 1`.

## Range (section `Range`)

* `mem_range_tensorEval`: a function `F : X → A` with values in a finite-dimensional
  subspace `D` lies in the range of `tensorEval e` once every coordinate function
  `x ↦ ψ (F x)`, `ψ ∈ D*`, is in the range of `e` (take `∑ b_j ⊗ s_j` over a basis of `D`).

## The smooth right regular representation (section `RightRegular`)

For a topological group `H`:

* `rightSmoothFunctions H`: functions `H → ℂ` invariant under right translation by some
  open subgroup; `rightRegular`: right translation on them (`rightRegular_isSmooth`).
* `rightRegularRep.{uV, uG}`: the same as a `SmoothRep` with carrier raised to
  `Type (max uG uV)` (by `universeLiftRepresentation`).
* `rightRegularEval`: evaluation of a vector as a function `H → ℂ`; it is injective
  (`rightRegularEval_injective`), turns the action into right translation
  (`rightRegularEval_equivariant`, by `rfl`), and hits every right-smooth function
  (`exists_rightRegularEval_eq`).

## Range condition (section `RangeCondition`)

* `translateEval_mem_range`: if `W` is smooth, `τ 0` is admissible and `e` hits every
  right-smooth function, every `translateEval W (τ 0) φ w` lies in the range of
  `finTwoEval e`. Proof: if `w` is fixed by an open subgroup `O` of `H 0 × H 1`, the
  values `φ (W (mulSingle 1 g) w)` are fixed by `O ∩ H 0` and so lie in the
  finite-dimensional space of `O ∩ H 0`-fixed vectors of `τ 0` (admissibility); the
  coordinate functions are right-invariant under `O ∩ H 1`; conclude by
  `mem_range_tensorEval`.
* `exists_external_ne_zero_of_smooth`: combines the previous item with
  `exists_external_ne_zero`.

## Fixed slices (section `FixedSlice`)

* `secondFixedSlice W K`: the vectors fixed by `K ≤ H 1` under the second factor, a
  subrepresentation of `W|_{H 0}` (the two factors commute:
  `mulSingle_zero_one_commute`); `mem_secondFixedSlice`.
* `isSmooth_secondFixedSlice`, `isAdmissible_secondFixedSlice`: smooth if `W` is; admissible
  if `W` is and `K` is open (the `K₁`-fixed vectors of the slice inject into the
  `K₁ × K`-fixed vectors of `W`).
* `exists_secondFixedSlice_isSubquotient`: if `W` is smooth, `H 1` has arbitrarily small
  compact open subgroups, and the irreducible `X` is a subquotient of `W|_{H 0}`, then `X`
  is a subquotient of `secondFixedSlice W K` for some compact open `K`. Proof: pick a
  vector `u` of the subrepresentation with nonzero image, a compact open `K` fixing `u` in
  the second factor; intersect the subrepresentation with the slice; the restricted
  quotient map is nonzero, hence surjective since `X` is irreducible.
* `exists_ne_zero_of_secondFixedSlice`: for compact open `K` (and `W` smooth over a field of
  characteristic zero), a nonzero `ψ : secondFixedSlice W K → X` extends to a nonzero
  `φ : W|_{H 0} → X`, namely `ψ ∘ P` with `P` the averaging projection onto the
  `K`-fixed vectors (`Compact.CharZero.fixedProjection`), which commutes with the first
  factor (`Compact.CharZero.averageMap_commute`).
* `exists_ne_zero_of_secondFixedSlice_of_surjective`: the same for a surjective `ψ` onto a
  nontrivial `X`.
