# The trivial grading and ungraded unitriangular matrix coefficients

Author: Worker 16, as a helper for task `27fe1be6-a9cb-4bc5-8f71-3af15cd3d92b`
(Renard VI.1.2 and VI.1.3 for represented parabolics). Module
`Langlands.Algebra.GradedHopf.TrivialGrading`, namespace `Langlands.Algebra.GradedHopf`.

## Provenance

Internal. The module derives an ungraded corollary of the published graded theorem
`exists_unitriangular_of_isUnipotent` (module `Langlands.Algebra.GradedHopf.UnipotentFlag`)
by applying it to the trivial `ℤ`-grading. Geometrically the corollary is the standard fact
that a unipotent affine group of finite type over a field embeds as a closed subgroup of
upper unitriangular matrices; the module proves only the Hopf-algebraic form stated below
and does not formalize the geometric statement. No source is cited.

## The trivial grading

For a commutative ring `k` and a commutative `k`-algebra `A`:

- `trivialGrade k A : ℤ → Submodule k A` sends `0` to `⊤` and every other degree to `⊥`.
- `trivialGrade_zero`, `trivialGrade_of_ne`, `mem_trivialGrade_zero` and
  `eq_zero_of_mem_trivialGrade` record these values: every element lies in degree `0`, and an
  element of a nonzero degree is `0`.
- `isInternal_trivialGrade` proves `DirectSum.IsInternal (trivialGrade k A)`, by
  `DirectSum.isInternal_submodule_of_iSupIndep_of_iSup_eq_top`: the family is independent
  because all but one member is `⊥`, and its supremum is `⊤` because degree `0` is `⊤`.
- `trivialGradedAlgebra : GradedAlgebra (trivialGrade k A)` is the graded-algebra structure.
  `1` lies in degree `0`; a product of homogeneous elements lies in the sum of their degrees
  because either both degrees are `0`, or one factor is `0`. The decomposition is
  `isInternal_trivialGrade.chooseDecomposition`. It is a `def` marked
  `@[instance_reducible]`, not a global instance, so it never competes with other gradings.

## Bialgebras

`isGradedBialgebra_trivialGrade` proves `IsGradedBialgebra (trivialGrade k A)` for a
`k`-bialgebra `A` and any `GradedAlgebra (trivialGrade k A)` instance. In degree `0` the
comultiplication lands in total degree `0` of the tensor grading: this is proved by
induction on the tensor `Coalgebra.comul a` (`TensorProduct.induction_on`), each pure tensor
lying in total degree `0 + 0` by the published `tmul_mem_tensorGrade`. In a nonzero degree
the element is `0`, so both the comultiplication condition and the counit condition hold.

## Main theorem

`exists_unitriangular_matrixCoefficients` takes a field `k : Type u`, a commutative Hopf
algebra `A : CommHopfAlgCat.{u} (CommRingCat.of k)` with `[Algebra.FiniteType k A]`, and
`hU : IsUnipotent ((hopfSpec (CommRingCat.of k)).obj (op A))`. It proves that there are
`n : ℕ` and a matrix `M : Matrix (Fin n) (Fin n) A` such that

- `Coalgebra.comul (M i j) = ∑ l, M i l ⊗ₜ M l j` for all `i j`;
- `Coalgebra.counit (M i j) = if i = j then 1 else 0` for all `i j`;
- the entries of `M` generate `A` as a `k`-algebra:
  `Algebra.adjoin k (Set.range fun p => M p.1 p.2) = ⊤`;
- `M` is upper unitriangular: `M i i = 1` for all `i`, and `M i j = 0` whenever `j < i`.

Proof: install `trivialGradedAlgebra`, apply `exists_unitriangular_of_isUnipotent A
(trivialGrade k A) isGradedBialgebra_trivialGrade hU`, and forget the grading of the
resulting `GradedMatrixCoefficients` structure `G`, reading off `G.comul_apply`,
`G.counit_apply`, `G.adjoin_eq_top` and the two unitriangularity facts.
