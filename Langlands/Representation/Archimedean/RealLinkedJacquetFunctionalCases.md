# The linked Jacquet functional statement by kinds of blocks

Module `Langlands.Representation.Archimedean.RealLinkedJacquetFunctionalCases`.

## What it states

`RealLinkedJacquetFunctionalStatement` (S2, module `RealLinkedJacquetFunctional`) asks, for a
list `ds` of real blocks of total rank `n` that is in Langlands order (`IsRealLanglandsOrdered`)
and has two linked Mœglin data (`¬ IsRealMoeglinUnlinked ds`), for

* a nonzero linear functional `ℓ` on the `O(n)`-finite functions of the standard module of `ds`
  that is a real Jacquet functional with exponents `a : Fin n → ℂ` and signs `e : Fin n → Fin 2`
  (`IsRealJacquetFunctional n (realStandardRep n ds) (realStandardLie n ds) ℓ a e`),
* a position `p` with `p + 1 < n` and `k : ℕ` with `a_p - a_{p+1} = 1 - k`,
* such that `ℓ(π(E_{p+1,p})^k v) = 0` for every `v`, where `π(E_{p+1,p})` is the action of
  `1 ⊗ lowerRootMatrix n p hp` through `realStandardLie n ds`.

This module states S2 separately for the two kinds of lists, with the same conclusion:

* `RealCharacterLinkedJacquetFunctionalStatement`: the lists all of whose blocks are real
  characters, `RealStrictCharacterLanglandsQuotient.IsCharacterList ds` (every block is
  `RealBlock.character c`). The standard module of such a list is a principal series of
  `GL_n(ℝ)`.
* `RealInducedLinkedJacquetFunctionalStatement`: the lists with `¬ IsCharacterList ds`, that is,
  with at least one induction block `RealBlock.induced`, whose factor of the standard module is
  induced from a character of `ℂ^×` (a discrete series of `GL_2(ℝ)` twisted by `|det|^s` when the
  weight is nonzero).

Apart from the added hypothesis `IsCharacterList ds`, respectively `¬ IsCharacterList ds`, both
statements are word for word S2.

## Proof of the reduction

`realLinkedJacquetFunctional_of_cases` proves S2 from the two statements: given `ds`, split on
whether `IsCharacterList ds` holds and apply the corresponding statement to the same data.

## Provenance

The split is internal to this project; it separates the case of principal series, where every
crossing of two adjacent position characters can be realized by a block Fourier multiplier
functional (`RealBlockJacquet.blockJacquet`, module `RealBlockJacquetFunctional`), from the case
with induction blocks, which needs the analysis of a discrete series block. The mathematical
argument for S2 in both cases, with its sources (Mœglin 1997, Knapp 1986 Chapter VII,
Bernstein–Gelfand 1980), is described in `RealLinkedJacquetFunctional.md`.
