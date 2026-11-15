# Swapping adjacent unlinked characters, from the case `GL_2(ℂ)`

Module `Langlands.Representation.Archimedean.ComplexStandardUnlinkedSwapReduction`. It imports
`ComplexBlockRestriction` (namespace `Langlands.Archimedean.ComplexBlock`, the restriction to a
`GL_2(ℂ)` block), the Library module `ComplexJacquetFrobeniusProof` (the Frobenius functions)
and the statement module `ComplexStandardUnlinkedSwap`.

## The statement

`ComplexStandardUnlinkedSwapReductionStatement` is the implication

`ComplexGLTwoUnlinkedIrreducibleStatement → ComplexStandardUnlinkedSwapStatement`.

* `ComplexGLTwoUnlinkedIrreducibleStatement` (module `ComplexGLTwoUnlinkedIrreducible`): for
  complex characters `d`, `e` that are not linked (`IsComplexLinked`), the
  `(𝔤𝔩_2(ℂ), U(2))`-module of `U(2)`-finite functions of the standard module of `[d, e]` is
  irreducible.
* `ComplexStandardUnlinkedSwapStatement` (module `ComplexStandardUnlinkedSwap`): for
  `(pre ++ d :: e :: post).length = n` and `d`, `e` not linked, there is a bijective
  intertwining map from `X(pre ++ e :: d :: post)` onto `X(pre ++ d :: e :: post)`. Here `X(cs)`
  is the space of `U(n)`-finite functions of the standard module of `cs`, and the map
  intertwines with the `(𝔤𝔩_n(ℂ), U(n))`-action on `X(pre ++ d :: e :: post)`.

The theorem `complexStandardUnlinkedSwapReduction` proves the implication.

Provenance. The source of the conclusion is Tadić 2009, as recorded in
`ComplexStandardUnlinkedSwap.md`. `δ_d × δ_e` is irreducible for unlinked `d`, `e` (p. 11), an
irreducible `σ₁ × σ₂` is isomorphic to `σ₂ × σ₁` (p. 6), and induction in stages (p. 5–6)
passes from `GL_2` to `GL_n`. The proof here is internal and avoids induction in stages, which
is awkward for abstract `(𝔤, K)`-maps of `K`-finite vectors. It uses the rank-one Jacquet
functional and the finite `K`-multiplicity arguments of the modules `ComplexSwapJacquet*` and
`ComplexPermutation*`, which prove `ComplexStandardPermutationStatement`. It adds Frobenius
reciprocity with the value at the identity and restriction to the `GL_2(ℂ)` block of the two
swapped characters.

## Frobenius reciprocity with the value at the identity

* `ComplexBlock.exists_frobenius_eval_one`: for a `(𝔤𝔩_n(ℂ), U(n))`-module `(ρ, π)` and a nonzero
  Jacquet functional `ℓ` with exponents `a`, `b`, there are characters `dd 0, …, dd (n-1)` with
  `2 t_j + (n - 1) - 2j = a_j` and `i l_j = b_j`, and an embedding `B` of `V` into
  `X(List.ofFn dd)` with `(B w)(1) = ℓ(w)` for every `w`. The construction is the one of the
  Library theorem `complexJacquetFrobenius`: `B w` is the Frobenius function
  `frobeniusFunction ρ ℓ l a w`. The new conclusion `(B w)(1) = ℓ(w)` is `frobeniusFunction_eq`
  at `1 = 1 · 1`, with `borelChar_one`.
* `ComplexBlock.exists_embedding_eval_one`: for a nonzero Jacquet functional `ℓ` on `X(ds)` with
  the exponents `listExponent n es hes`, `listWeight n es hes` of a list `es` of length `n`,
  there is an embedding `S : X(ds) → X(es)` (`IsComplexStandardEmbedding`) with
  `(S f)(1) = ℓ(f)`. The characters `dd` are those of `es` by `eq_of_params`, as in
  `ComplexPermutation.exists_embedding_of_jacquet`.

## The swap embedding is bijective

`ComplexBlock.exists_bijective_embedding` takes `ComplexGLTwoUnlinkedIrreducibleStatement`,
`(pre ++ d :: e :: post).length = n`, `0 ≤ Re(t_d - t_e)`, `(l_d, t_d) ≠ (l_e, t_e)` and
`¬ IsComplexLinked d e`. It gives a bijective embedding `S : X(ds) → X(es)` with
`ds = pre ++ d :: e :: post` and `es = pre ++ e :: d :: post`. The proof uses the block at
`p = pre.length`:

1. `exists_lamTwo_ne_zero` gives `c` with `Λ_c^{(2)} ≠ 0` on the block. The key lemma
   `eq_bot_of_lamN` then applies to every stable subspace of `X(ds)` on which `Λ_c^{(n)}`
   vanishes.
2. `Λ_c^{(n)} ≠ 0`. Otherwise the key lemma for `W = ⊤` gives `X(ds) = 0`. But
   `ComplexSwapJacquet.exists_integral_integrand_ne_zero` gives some `f ∈ X(ds)` and some `c'`
   with `Λ_{c'}^{(n)}(f) ≠ 0`, so `f ≠ 0`.
3. `isJacquet_lamN` and `exists_embedding_eval_one` give an embedding `S : X(ds) → X(es)` with
   `(S f)(1) = Λ_c^{(n)}(f)`.
4. `S` is injective. `S` is an intertwining map (`ComplexPermutation.intertwining_of_embedding`),
   so `ker S` is stable under `U(n)` and the Lie algebra. On `ker S`,
   `Λ_c^{(n)}(f) = (S f)(1) = 0`. The key lemma gives `ker S = ⊥`.
5. `S` is surjective by `ComplexPermutation.surjective_of_injective_of_kMap`, using the injective
   `U(n)`-equivariant map `X(es) → X(ds)` of `ComplexPermutation.exists_kMap_swap`. The
   `U(n)`-types have finite and equal multiplicities.

`ComplexPermutation.exists_bijective_swap` gets injectivity from the irreducibility of `X(ds)`.
Here it comes instead from the irreducibility on the `GL_2(ℂ)` block, through the key lemma.

## Proof of the reduction

`complexStandardUnlinkedSwapReduction`: let `d`, `e` be unlinked with
`(pre ++ d :: e :: post).length = n`. There are three cases.

* `l_d = l_e` and `t_d = t_e`: then `d = e` (`eq_of_params`), the two lists are equal, and the
  identity works (`isComplexStandardIntertwining_id`).
* `0 ≤ Re(t_d - t_e)`: `exists_bijective_embedding` gives a bijective embedding
  `S : X(ds) → X(es)`. Its inverse is a bijective intertwining map `X(es) → X(ds)`
  (`ComplexPermutation.intertwining_symm_of_embedding`).
* `Re(t_d - t_e) ≤ 0`: `e`, `d` are unlinked (`isComplexLinked_symm`), and
  `exists_bijective_embedding` for `(e, d)` gives a bijective embedding `S : X(es) → X(ds)`. It
  is an intertwining map `X(es) → X(ds)` for the action on `X(ds)`
  (`ComplexPermutation.intertwining_of_embedding`).

There is no condition on the real parts of the exponents, and none on the other characters.
