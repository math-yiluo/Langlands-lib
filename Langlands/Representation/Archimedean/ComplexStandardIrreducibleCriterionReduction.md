# Reducing the irreducibility criterion ("if" part) for `GL_n(ℂ)` to unlinked swaps

Lean module: `Langlands.Representation.Archimedean.ComplexStandardIrreducibleCriterionReduction`.
Worker 728 wrote it under Task 7064. It is the complex counterpart of the Library module
`RealStandardIrreducibleCriterionReduction`.

The Library statement `Langlands.Archimedean.ComplexStandardIrreducibleCriterionStatement` (Sp_C,
module `ComplexLargeStandardIrreducibleSplit`, Task 7102) is the "if" direction of the
irreducibility criterion for principal series of `GL_n(ℂ)` (Tadić 2009, §3). Let `ds` be a list
of `n` complex characters with `IsComplexLanglandsOrdered ds` and `IsComplexUnlinked ds`. Then the
standard module of `ds` is an irreducible `(𝔤, K)`-module.

This module states one new statement, Rev_C below, and proves that it implies Sp_C together with
the published swap statement `ComplexStandardUnlinkedSwapStatement` (T5, module
`ComplexStandardUnlinkedSwap`). The implication is `complexStandardIrreducibleCriterionReduction`.
It adds no hypothesis to Sp_C. Rev_C is only stated here; it still needs a proof.

Notation: `I(ds)` is the `(𝔤𝔩_n(ℂ), U(n))`-module `(complexStandardRep n ds, complexStandardLie n ds)`
on `kFiniteFunctions (complexStandardModule n ds) (unitaryCompact ℂ n)`. An intertwiner
`T : I(ds) → I(es)` is a `ℂ`-linear map with
`IsComplexStandardIntertwining n (complexStandardRep n es) (complexStandardLie n es) ds T`.

## The new statement

`ComplexReverseIntertwinerKernelStatement` (Rev_C). Let `ds` be a list of `n` complex characters
with `IsComplexLanglandsOrdered ds` (non-increasing real parts of the exponents). Let
`T : I(ds) → I(ds.reverse)` be any intertwiner and `W` any `(𝔤, K)`-submodule of `I(ds)`
(`IsGKSubmodule`) with `W ≠ ⊤`. Then `W ≤ ker T`.

Source and why it is true. This is a consequence of Langlands' classification. Wallach 1979,
Theorem 6.7 (p. 80, Langlands' theorem), states it for a parameter in the open positive chamber:
the principal series induced from the opposite Borel subgroup has a unique nonzero irreducible
submodule. Here that principal series is `I(ds.reverse)`, and its submodule is the Langlands
quotient `J` of `I(ds)`. The Library's real counterpart `RealStandardIrreducibleCriterionReduction.md`
gives two more facts, citing Mœglin 1997, Theorem 4, and Knapp 1986, Theorems 8.54 and 7.24 and
Proposition 8.61: `J` occurs with multiplicity one in `I(ds)`, and `J` is the image of the long
intertwining operator. Given these facts, a nonzero `T` has as image a quotient of `I(ds)` that
contains `J`. By multiplicity one the image equals `J`, so `ker T` is the largest proper submodule
and contains every proper `W`. When some exponents have equal real parts, the characters with equal
real exponent form a tempered block. For `GL_n(ℂ)` the order inside such a block does not matter,
as in the real case. A proof of Rev_C must establish all of this; this module only states it.

## The reduction

`ComplexStandardIrreducibleCriterionReductionStatement` is the Prop
`ComplexStandardUnlinkedSwapStatement → ComplexReverseIntertwinerKernelStatement →
ComplexStandardIrreducibleCriterionStatement`. Its proof `complexStandardIrreducibleCriterionReduction`
works as follows.

* `ComplexInjectiveIntertwinerExists n ds es` says that there is an injective intertwiner
  `I(ds) → I(es)`. It is reflexive (identity) and transitive. Transitivity composes the maps with
  the Library lemma `IsComplexStandardIntertwining.comp`, using `map_complexStandardRep` and
  `map_complexStandardLie` of the second map.
* `isComplexLinked_comm`: `IsComplexLinked` is symmetric (negate `p` and `q`).
* `complexInjectiveIntertwinerExists_moveToEnd`: if `a` is unlinked from every element of `l`, then
  `I(pre ++ a :: l ++ post) → I(pre ++ l ++ a :: post)` exists. By induction on `l`, each step is
  T5 for the adjacent pair `a`, `b` (bijective, hence injective). T5 needs no order of the real
  exponents.
* `complexInjectiveIntertwinerExists_reverse`: if `l` is pairwise unlinked, then
  `I(pre ++ l ++ post) → I(pre ++ l.reverse ++ post)` exists. Move the head to the end, then
  reverse the rest.
* `complexStandardIrreducibleCriterionReduction`: since `IsComplexUnlinked ds` is
  `ds.Pairwise (¬ IsComplexLinked · ·)`, there is an injective intertwiner
  `T : I(ds) → I(ds.reverse)`. `I(ds)` is nonzero (Library `complexStandardNontrivial`). By Rev_C,
  every proper `(𝔤, K)`-submodule lies in `ker T = ⊥`.

Unlike the real reduction, this one needs neither the Langlands-quotient statement nor an order
condition on the swaps: the complex swap statement T5 gives bijections for unlinked pairs in
both orders.
