# Iterated differences on the compact picture of a real standard module

Let `Std = Automorphic.realStandardKFinite n ds` be the `O(n)`-finite standard module of a real
block list `ds`, with the right translation action `realStandardRep n ds` of the orthogonal
group.

## Definitions

* `rightDifference k = realStandardRep n ds k - 1` for an orthogonal matrix `k`;
* `iteratedDifference ks` is the ordered product of the differences of a list `ks` of
  orthogonal matrices;
* `displacementProduct ks = Π_{k ∈ ks} ‖k - 1‖` (operator norms), which is nonnegative
  (`displacementProduct_nonneg`);
* `CompactDifferenceBound J f R`: for every list `ks` of length at most `J`, the vector
  `iteratedDifference ks f` satisfies `CompactBound` (of `RealCompactProbeBounds`) with
  constant `R · displacementProduct ks`.

## Elementary properties

* `CompactDifferenceBound.value`: the empty list gives `CompactBound f R`; in particular
  `R ≥ 0` (`constant_nonneg`). `mono` enlarges the constant.
* `CompactDifferenceBound.rightDifference`: a bound of order `J + 1` gives, for every list of
  length at most `J`, the first right difference bound `CompactRightDifferenceBound` of the
  iterated difference with constant `R · displacementProduct ks` (prepend one more move).
* `iteratedDifference_commutes`: an endomorphism commuting with all compact right translations
  commutes with every iterated difference.
* `CompactDifferenceBound.residual`: if such an endomorphism `A` satisfies
  `CompactBound v M → CompactBound (A v) (C M)`, then a bound of order `J` for `f` gives a
  bound of order `J` for `f - A f` with constant `(1 + C) R`.
* `CompactDifferenceBound.residual_succ`: if `A` commutes with compact translations and
  satisfies the approximate-identity error bound
  `CompactBound (v - A v) (C ε (R + D))` whenever `v` has value bound `R` and first difference
  bound `D`, then a bound of order `J + 1` for `f` gives a bound of order `J` for `f - A f`
  with constant `2 C ε R`.

## Orbit bound

`CompactEquivariantOrbitBoundStatement`: for every standard vector `f` and every linear
functional `ℓ` on `Std` there is `S ≥ 0` such that `‖ℓ(T f)‖ ≤ S R` for every endomorphism `T`
commuting with compact right translations and every `R` with `CompactBound (T f) R`.

`compactEquivariantOrbitBound` proves it. Let `V` be the span of the compact orbit of `f`; it
is finite-dimensional by the compact-finiteness conjunct (every vector is `O(n)`-finite) of
`isRealGKModule_realStandardModule`. For such `T`, the restriction of `T f` to `O(n)` is
`k ↦ λ(ρ(k) f)` with the functional `λ = (evaluation at 1) ∘ T` on `V`; these restrictions lie
in the image of the finite-dimensional dual of `V`. Restriction to the orthogonal group is
injective on the principal series (`eq_of_eqOn_unitaryCompact_of_mem_principalSeries`), so the
vectors whose restriction lies in that image form a finite-dimensional space `W` on which
compact point evaluations separate points. On `W` the functional `ℓ` is a finite linear
combination `Σ c_j f(p_j)` of compact point evaluations (`exists_sum_of_separating`), and
`S = Σ ‖c_j‖` works.

This is the real counterpart of the Library's `ComplexCompactDifferences`, used in
`RealWhittakerFiniteOrder`.
