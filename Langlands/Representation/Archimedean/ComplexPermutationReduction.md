# Permutation invariance from adjacent swaps

Module `Langlands.Representation.Archimedean.ComplexPermutationReduction`, namespace
`Langlands.Archimedean.ComplexPermutation`.

`complexStandardPermutation_of_swapJacquet` proves that `SwapJacquetStatement` (rank-one Jacquet
functionals, `ComplexPermutationSwap`) and `ComplexJacquetFrobeniusStatement.{0}` (Frobenius
reciprocity) imply `ComplexStandardPermutationStatement`.

## Declarations

* `SwapReachable n l₁ l₂` (Prop-valued definition, internal): for every prefix `pre` with
  `(pre ++ l₁).length = n`, if the `U(n)`-finite functions of the standard module of
  `pre ++ l₁` form an irreducible module, there is a bijective intertwining map from those of
  `pre ++ l₂` onto them.
* `swapReachable_of_perm`: `l₁.Perm l₂ → SwapReachable n l₁ l₂`, by induction on `List.Perm`:
  * `nil`: the identity map (`isComplexStandardIntertwining_id`);
  * `cons x`: the induction hypothesis with the longer prefix `pre ++ [x]`;
  * `swap x y l`: one adjacent swap, `exists_bijective_swap` for `pre ++ y :: x :: l`;
  * `trans`: the first map `T₁ : X(pre ++ l₂) → X(pre ++ l₁)` is bijective. So `X(pre ++ l₂)`
    is nontrivial and, by `isIrreducibleGKModule_of_injective`, irreducible. The second
    induction hypothesis then gives `T₂ : X(pre ++ l₃) → X(pre ++ l₂)`, and `T₁ ∘ T₂` is
    bijective and intertwining (`IsComplexStandardIntertwining.comp`).
* `complexStandardPermutation_of_swapJacquet`: given `ds.length = n`, `es.Perm ds` and
  irreducibility of the standard module of `ds`, apply `swapReachable_of_perm` to
  `ds.Perm es` with the empty prefix.
