# Permutation invariance for one adjacent swap

Module `Langlands.Representation.Archimedean.ComplexPermutationSwap`, namespace
`Langlands.Archimedean.ComplexPermutation`.

Let `ds = pre ++ d :: e :: post` and `es = pre ++ e :: d :: post`, of length `n`. The theorem
`exists_bijective_swap` says: if the `U(n)`-finite functions `X(ds)` of the standard module of
`ds` form an irreducible `(𝔤𝔩_n(ℂ), U(n))`-module, there is a bijective intertwining map
`T : X(es) → X(ds)` (`IsComplexStandardIntertwining` for the module `X(ds)`). This is the
intertwining-operator route named in the objective of `ComplexStandardPermutationStatement`.
The rank-one intertwining operator enters only through its Jacquet functional
(`SwapJacquetStatement`).

## The statement `SwapJacquetStatement`

`listExponent n es hes j = 2 t_j + (n - 1) - 2 j` and `listWeight n es hes j = i l_j`, where
`t_j` and `l_j` are the exponent and weight of the `j`-th character of a list `es` of length
`n`. For `es` itself these are the Jacquet exponents of evaluation at `1` on `X(es)`.

`SwapJacquetStatement` (a Prop-valued definition): for every `pre`, `post`, `d`, `e`, `n` with
`(pre ++ d :: e :: post).length = n`, `0 ≤ Re (t_d - t_e)` and `(l_d, t_d) ≠ (l_e, t_e)`, there
is a nonzero linear functional `ℓ` on `X(pre ++ d :: e :: post)` with
`IsComplexJacquetFunctional n (complexStandardLie n (pre ++ d :: e :: post)) ℓ a b`. Here `a`
and `b` are `listExponent` and `listWeight` of `pre ++ e :: d :: post`. In the proof
(`ComplexSwapJacquetFunctional`, `ComplexSwapJacquetNonvanishing`), `ℓ` is the rank-one integral
`f ↦ ∫_ℂ (R(c E_jj) f - κ_j(c) f)(s x(z)) dz` at the positions `i = pre.length`, `j = i + 1`,
where `s` is the permutation matrix of `(i j)` and `x(z) = 1 + z E_ij`. This is the value at `1`
of the standard intertwining operator for the simple reflection at `pre.length`, applied to
`R(c E_jj) f - κ_j(c) f`. That function vanishes at `1`, so the integral converges absolutely
also on the line `Re t_d = Re t_e`.

## Auxiliary results

* `complexPositionCharacter_eq_get`, `complexPositionCharacter_of_length_le`,
  `complexPositionCharacter_congr`: the position characters of a list are read off its entries.
  Two lists of the same length with the same characters have the same position characters.
* `character_eq_of_params`, `eq_of_params`: weight and exponent determine the character (by
  `character_eq`), hence the whole `ComplexCharacterData`.
* `kfEquiv`: the identity on functions between the `U(n)`-finite functions of two lists with
  equal position characters.
* `intertwining_of_embedding`: an embedding `S : X(ds) → X(es)` (`IsComplexStandardEmbedding`)
  is an intertwining map from `X(ds)` into the module `X(es)`.
  `equivariant_of_intertwining`: the `U(n)`-equivariance of an intertwining map.
  `intertwining_symm_of_embedding`: the inverse of a bijective embedding `X(ds) → X(es)` is an
  intertwining map `X(es) → X(ds)`.
* `swapPerm`, `get_swap`, `exists_kMap_swap`: with `σ` the transposition of the positions
  `pre.length` and `pre.length + 1`, `List.ofFn (fun k => ds[σ⁻¹ k]) = es`. So `permKMap`
  (`ComplexPermutationKMap`) gives an injective `U(n)`-equivariant map `X(ds) → X(es)`; by
  symmetry there is also one `X(es) → X(ds)`.
* `exists_embedding_of_jacquet`: Frobenius reciprocity (`ComplexJacquetFrobeniusStatement`)
  applied to a nonzero Jacquet functional on `X(ds)` with exponents `listExponent`/`listWeight`
  of `es` gives a nonzero embedding `X(ds) → X(List.ofFn dd)`. The equations
  `2 t'_j + (n - 1) - 2j = a_j` and `i l'_j = b_j` give `dd j = es[j]` (`eq_of_params`), so
  `List.ofFn dd = es`.

## Proof of `exists_bijective_swap`

* If `l_d = l_e` and `t_d = t_e`, then `d = e`, `es = ds`, and `T` is the identity
  (`isComplexStandardIntertwining_id`).
* If `Re t_d ≥ Re t_e`: `SwapJacquetStatement` and Frobenius reciprocity give a nonzero embedding
  `S : X(ds) → X(es)`. It is injective, its kernel being an invariant subspace of the
  irreducible `X(ds)` (`injective_of_isIrreducibleGKModule`). It is surjective by
  `surjective_of_injective_of_kMap` with the injection `X(es) → X(ds)` of `exists_kMap_swap`.
  `T = S⁻¹` (`intertwining_symm_of_embedding`).
* If `Re t_d ≤ Re t_e`: `SwapJacquetStatement` for `es` (the roles of `d` and `e` exchanged)
  and Frobenius reciprocity give a nonzero embedding `S : X(es) → X(ds)`, an intertwining map
  into the module `X(ds)`. Its range is a nonzero invariant subspace of the irreducible `X(ds)`,
  so `S` is surjective. It is injective by `injective_of_surjective_of_kMaps` with the two
  injections of `exists_kMap_swap`. `T = S`.
