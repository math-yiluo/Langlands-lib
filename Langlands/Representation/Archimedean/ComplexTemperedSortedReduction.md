# Tempered irreducibility reduced to weight-sorted lists

Lean module: `Langlands.Representation.Archimedean.ComplexTemperedSortedReduction`.

Worker 5677 wrote this module, with Worker 728 as coauthor. It is part of Task 7064
(`e4a22cc7-0a28-44a3-afc6-38bb7c243851`). An operator request
(`6f5a21aad63b5328a7798c7b491d09e4`) assigned the Library statement
`ComplexTemperedStandardIrreducibleStatement` (written U below) to Worker 728 inside Task 7064.
Worker 728's route to U handles lists of characters whose weights do not decrease along the
list (the minimal-`U(n)`-type vector is then a product of minors). This module removes that
sorting condition.

Notation. A complex character `d : ComplexCharacterData` has an integer `weight` and a complex
`exponent`, and is `z ↦ (z/|z|)^weight · |z|^(2·exponent)`. For a list `ds` of `n` characters,
`X(ds)` is the `(𝔤𝔩_n(ℂ), U(n))`-module `(complexStandardRep n ds, complexStandardLie n ds)` of
`U(n)`-finite functions of `complexStandardModule n ds`. `IsComplexLinked d e` and
`IsComplexUnlinked ds` (no two characters of `ds` linked) are the Library definitions from
`ComplexLargeStandardIrreducibleSplit`.

## The statement

`Langlands.Archimedean.ComplexTemperedSortedReductionStatement`: assume that for every `n`
and every list `ds` of length `n` such that

* all exponents of `ds` have the same real part, and
* the weights do not decrease along `ds` (`ds.Pairwise (fun d e => d.weight ≤ e.weight)`),

`X(ds)` is irreducible (`IsIrreducibleGKModule`). Then `ComplexTemperedStandardIrreducibleStatement`
holds: `X(ds)` is irreducible for every list `ds` of length `n` whose exponents all have the
same real part, in any order.

It is proved here as `Langlands.Archimedean.complexTemperedSortedReduction`, with no other
hypotheses.

Provenance. This is an internal reduction statement. U is the Library statement (Badulescu–Renard
2010, Theorem 3.1 with §9.1). Its source makes no use of this reduction. The sorting step
uses two facts: a permutation of a pairwise unlinked list gives an isomorphic standard module
(Tadić 2009, p. 11 and p. 6, the Library statement `ComplexStandardUnlinkedSwapStatement`),
and characters whose exponents have equal real parts are not linked.

## Further exported results

* `Langlands.Archimedean.complexStandardIrreducible_of_perm n ds ds' hlen hperm hunl hirr`:
  suppose `ds'` has length `n`, `ds'` is a permutation of `ds` (`ds'.Perm ds`), `ds'` is
  pairwise unlinked, and `X(ds')` is irreducible. Then `X(ds)` is irreducible. This result is
  unconditional.
* `ComplexTemperedSorted.not_linked_of_re_eq`: if `d.exponent.re = e.exponent.re`, then
  `¬ IsComplexLinked d e`.
* `ComplexTemperedSorted.isComplexUnlinked_of_re_eq`: a list whose exponents all have the same
  real part is pairwise unlinked.
* `ComplexTemperedSorted.not_linked_symm`: linkage is symmetric.

## Proof

* `not_linked_of_re_eq`. A linkage gives integers `p`, `q` with `0 < p q`,
  `(t_d + w_d/2) − (t_e + w_e/2) = p` and `(t_d − w_d/2) − (t_e − w_e/2) = q`. Adding the two
  equations gives `p + q = 2(t_d − t_e)`. Its real part is `0`, so `q = −p` and
  `p q = −p² ≤ 0`, a contradiction.
* `irreducible_swap`. If `d`, `e` are not linked, the swap statement gives a bijective
  intertwining map `T : X(pre ++ e :: d :: post) → X(pre ++ d :: e :: post)`. The swap
  statement is `ComplexStandardUnlinkedSwapStatement`, used as the proved Library theorem
  `complexStandardUnlinkedSwapReduction complexGLTwoUnlinkedIrreducible`. If the target is
  irreducible, the source is nontrivial (two distinct preimages of two distinct elements). The
  Library lemma `isIrreducibleGKModule_of_injective` then shows that the source is irreducible.
* `irreducible_of_perm_append`. Fix a pairwise unlinked list `l₁` and a permutation
  `l₁ ~ l₂`. By induction on the permutation, for every prefix `pre`, irreducibility of
  `X(pre ++ l₁)` implies irreducibility of `X(pre ++ l₂)`.
  - Empty lists: nothing to do.
  - Equal heads: move the head into the prefix (`List.append_cons`).
  - A swap `y :: x :: l ~ x :: y :: l`: `irreducible_swap` with `d = y` and `e = x`. These are
    not linked because `y :: x :: l` is pairwise unlinked.
  - Transitivity: lengths are preserved under permutation, and so is pairwise unlinkedness,
    since linkage is symmetric (`not_linked_symm`, `List.Perm.pairwise`).
* `complexStandardIrreducible_of_perm` is the case `pre = []`.
* `complexTemperedSortedReduction`. Given `ds` with exponents of equal real part, let `ds'` be
  `ds.mergeSort` for the weight order. Then `ds'` is a permutation of `ds`
  (`List.mergeSort_perm`), its weights do not decrease (`List.pairwise_mergeSort`; the order
  is total and transitive), it has the same length and the same members, so its exponents
  have equal real parts. The hypothesis gives irreducibility of `X(ds')`.
  `isComplexUnlinked_of_re_eq` and `complexStandardIrreducible_of_perm` transfer it to `X(ds)`.
