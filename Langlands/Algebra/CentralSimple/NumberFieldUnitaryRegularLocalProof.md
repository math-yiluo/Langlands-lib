# Proof: regular local unitary elements of prescribed relative reduced norm

Module: `Langlands.Algebra.CentralSimple.NumberFieldUnitaryRegularLocalProof`.

`Langlands.CentralSimple.numberFieldUnitaryRegularLocal` proves
`Langlands.CentralSimple.NumberFieldUnitaryRegularLocalStatement.{u}` (module
`Langlands.Algebra.CentralSimple.NumberFieldUnitaryRegularLocalStatement`) in every universe
`u`: for a number field `F`, a separable quadratic extension `E/F`, a central simple
`E`-algebra `B` of degree `n` with an involution `τ` of the second kind and a place `v` of `F`,
a unitary point of `F_v ⊗[F] B` of relative reduced norm `z ⊗ 1` yields a unitary `x` and a
monic conjugate-reciprocal polynomial `f` of degree `n` over `F_v ⊗[F] E` with `f(x) = 0`,
`f'(x)` a unit and `1, x, …, x^{n-1}` independent over `F_v ⊗[F] E`.

## Auxiliary results

- `nonempty_algHom_or_isField_tensor`: for `finrank F E = 2` and a field `K` over `F`, either
  there is an `F`-algebra map `E → K` or `E ⊗[F] K` is a field. Let `m` be a maximal ideal of
  the two-dimensional `K`-algebra `K ⊗[F] E`. If the quotient has dimension `1`, it is `K` and
  `E → K ⊗[F] E → K` is the map. If it has dimension `2`, the quotient map is injective, so
  `K ⊗[F] E` is a field, and so is `E ⊗[F] K`.
- `Langlands.FieldTheory.isAlgClosed_of_ringEquiv`: Mathlib's `IsAlgClosed.of_ringEquiv` with the two fields in
  different universes.
- `isAlgClosed_of_finrank_eq_two`: every field `L` of dimension `2` over the completion `F_w`
  at an infinite place is algebraically closed. Extend the embedding `F_w → ℂ`
  (`InfinitePlace.Completion.extensionEmbedding`, whose image contains `ℝ` by
  `surjective_extensionEmbeddingOfIsReal` and `surjective_extensionEmbedding_of_isComplex`) to
  `g : L → ℂ` (`IsAlgClosed.lift`). An element `ℓ ∉ F_w` has `g(ℓ)` non-real, so `i` and hence
  all of `ℂ` lie in the image of `g`; thus `L ≅ ℂ`.
- `unitaryInvolutionSplitting_infinitePlace`: `UnitaryInvolutionSplitting F_w` at every
  infinite place, from the previous result and Mathlib's
  `IsSimpleRing.exists_algEquiv_matrix_of_isAlgClosed`.

## The proof

Let `v` be a place and `K = F_v`. At an infinite place `K = w.Completion` with the norm of
`NormedField` and nontriviality from the isometric embedding into `ℂ`; at a finite place
`K = FiniteCompletion F v` with `Valued.toNontriviallyNormedField`. Both are complete of
characteristic zero. By `nonempty_algHom_or_isField_tensor`:

- if there is `φ : E → K` over `F`, `K` becomes an `E`-algebra through `φ` and
  `exists_regular_unitary_of_split` (module `Langlands.Algebra.CentralSimple.UnitaryRegularSplit`)
  gives the conclusion;
- if `E ⊗[F] K` is a field, `exists_regular_unitary_of_isField` (module
  `Langlands.Algebra.CentralSimple.UnitaryRegularNonsplit`) gives the conclusion, with
  `UnitaryInvolutionSplitting K` from `unitaryInvolutionSplitting_infinitePlace` at infinite
  places and from `Langlands.Algebra.CentralSimple.unitaryDivisionSplitting` and
  `Langlands.localUnitaryDivisionCommutative` (with `FiniteCompletion.valuativeRel` and
  `FiniteCompletion.isNonarchimedeanLocalField`) at finite places.

## Sources

- Martin Kneser, *Lectures on Galois Cohomology of Classical Groups*, TIFR Lectures on
  Mathematics 47 (1969), §5.6, Step 1, printed pp. 79–80 (PDF pp. 85–86), which treats the
  places split and not split in the quadratic extension separately, as here. Source
  `kneser-1969-galois-cohomology-classical-groups`.
- V. Platonov and A. Rapinchuk, *Algebraic Groups and Number Theory* (1994), proof of
  Theorem 6.28, printed pp. 363–364 (PDF pp. 373–374), the assumption that the local solutions
  are regular, and relations (6.44). Source
  `platonov-rapinchuk-1994-algebraic-groups-number-theory`.
