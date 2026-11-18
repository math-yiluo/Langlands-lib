# The scalar commutant for tied real standard modules without discrete series

Lean module: `Langlands.Representation.Archimedean.RealTiedScalarAssembly`. Author: Worker 379,
for Task 7626 (`4fda7898-2fbf-4ad2-a6b5-48fb114ca3e0`), whose target is
`Langlands.Archimedean.RealTemperedScalarCommutantStatement`. The statement
`RealTiedNondiscreteReductionStatement` and the theorem `realTiedNondiscreteReduction` are in the
namespace `Langlands.Archimedean`. All other declarations are in
`Langlands.Archimedean.RealTiedScalarAssembly`.

## Purpose and provenance

This module proves `HasScalarCommutant n ds` for every list `ds` of real blocks that has total
rank `n`, equal real exponents and no discrete-series block, given one hypothesis. A
discrete-series block is an induction block of nonzero weight (`IsRealDiscreteSeriesBlock`,
module `RealTiedScalarCommutantCases`). The hypothesis is Worker 48's
`RealSphericalCyclicStatement` (module `RealSphericalCyclic`): cyclicity of the `O(n)`-fixed
vector in spherical principal series in the closed Langlands chamber. Its provenance (Kostant's
cyclicity theorem as quoted by Wallach 1971) is explained in `RealSphericalCyclic.md`.

The declaration of record is the implication

`RealTiedNondiscreteReductionStatement : Prop :=
  RealSphericalCyclicStatement → RealTiedNondiscreteScalarCommutantStatement`,

and `realTiedNondiscreteReduction` proves it. Lists with discrete-series blocks are not covered
(that is `RealTiedDiscreteScalarCommutantStatement`). So this module does not prove the target.

Provenance. The implication and all declarations here are internal; the argument follows
Wallach (1971), Theorem 3.2, as explained in `RealTiedMinorProduct.md`. Two Library inputs are
used:

* `realUnlinkedSwap` (module `RealLinkedLanglandsQuotientNotLargeProof`). It is assembled from
  four proved swap theorems for adjacent unlinked blocks and does not depend on any
  Langlands-quotient or tempered-irreducibility statement.
* Mœglin's linking condition, `MoeglinDatum.IsLinked` (module
  `RealLargeStandardIrreducibleReduction`; Mœglin 1997, Theorem 10b, printed p. 164). Let `s`
  and `s'` be the exponents of the two data. In each case of `IsLinked`, `s - s'` is real and
  nonzero, with the following magnitude:
  - two characters: `s - s'` is a nonzero integer, of the parity fixed by the two signs;
  - a discrete datum `(2, s, D_p)` and a character: `|s - s'| = k + p/2` for a positive
    integer `k`;
  - two discrete data `(2, s, D_p)` and `(2, s', D_p')`: `|s - s'| = k + |p - p'|/2` for a
    positive integer `k`.

  In particular, data whose exponents have equal real parts are never linked.

## Notation

As in `RealTiedMinorScalar.md` and `RealTiedMinorProduct.md`. `RealInjectiveIntertwinerExists n
ds es` (Library, `RealStandardIrreducibleCriterionReduction`) says that there is an injective
linear map `KF n ds → KF n es` commuting with `O(n)` and the Lie algebra.
`EndomorphismsAreScalar ρ π` (Library `GKModuleOrthogonal`) says that every endomorphism
commuting with `ρ` and `π` is a scalar. `realBlockExponent x` is the real part of the exponent
of the block `x`. `IsRealLanglandsOrdered` (Library, `RealGenericParameterReduction`) says that
these real parts do not increase along the list.

## The hypothesis

`RealSphericalCyclicStatement` (Worker 48, module `RealSphericalCyclic`). Let `n : ℕ` and
`ds : List RealCharacterData` with `ds.length = n`, `d.parity = 0` for every `d ∈ ds`, and
`IsRealLanglandsOrdered (ds.map RealBlock.character)`. Let `T` be a nonzero element of
`KF n (ds.map RealBlock.character)` fixed by every `realStandardRep n _ k`. Then every subspace
`W` that contains `T` and is stable under every `realStandardLie n _ Z` is `⊤`.

## Results

Transfer.

* `endomorphismsAreScalar_of_injective`: let `T : V₁ → V₂` and `S : V₂ → V₁` be injective
  linear maps that intertwine the group actions and the Lie actions. If `EndomorphismsAreScalar`
  holds for `V₁`, it holds for `V₂`. Proof: `S T = d` and `S E T = c` for scalars `c`, `d`.
  If `d = 0`, then `V₁ = 0` and `V₂ = 0`. Otherwise `T S = d` on `V₂`, which gives
  `d² E = c d`, so `E = c/d`.
* `hasScalarCommutant_of_twoWay`: the same for `HasScalarCommutant`, with injective
  intertwiners `KF n ds → KF n es` and back.

Tied blocks are unlinked.

* `datumExponent`: the exponent `s` of a Mœglin datum.
* `not_isLinked_of_re_eq`: Mœglin data whose exponents have equal real parts are not linked.
  Proof: take real parts in the equation of each case of `IsLinked`. For two characters,
  `s - s' = k` with `k ≠ 0` an integer, so `Re s - Re s' = k ≠ 0`. In the other three cases one
  of `s - s'` and `s' - s` equals `q/2 + k` with `q` a natural number (`q = p` or
  `q = |p - p'|`) and `k` a positive integer. Its real part `q/2 + k` is positive, so
  `Re s ≠ Re s'`.
* `datumExponent_re_of_mem`, `areRealBlocksUnlinked_of_eq`: the Mœglin data of a block have the
  real exponent of the block. So two blocks with equal real exponents are unlinked
  (`AreRealBlocksUnlinked`).

Permutations.

* `realInjectiveIntertwinerExists_perm`: let `l₁` be a permutation of `l₂` with all real
  exponents of `l₁` equal to `r`. For every prefix `pre` with `realRank (pre ++ l₁) = n`, there
  is an injective intertwiner from `pre ++ l₁` to `pre ++ l₂`. The proof is induction on
  `List.Perm`. The `cons` case moves the head into the prefix, `swap` is `realUnlinkedSwap`
  (equal exponents, unlinked by `areRealBlocksUnlinked_of_eq`), and `trans` composes.
* `hasScalarCommutant_perm`: `HasScalarCommutant` is invariant under permutations of tied lists,
  by `hasScalarCommutant_of_twoWay`.

Character lists.

* `mem_signSet_iff`, `isBottom_signSet`: for a list of characters whose parities weakly
  increase, the odd positions form a bottom segment.
* `realPositionExponent_map_character_re`: in a list of characters with real exponents `r`,
  every position exponent has real part `r`.
* `hasScalarCommutant_sorted`: let `cs` be a list of characters of length `n` with all real
  exponents `r` and weakly increasing parities. Then `HasScalarCommutant n (cs.map character)`,
  given `RealSphericalCyclicStatement`. Proof: apply `hasScalarCommutant_of_cyclic`
  (`RealTiedMinorScalar`) and `eq_top_of_sphCyclic` (`RealTiedMinorProduct`). Let `A` be the
  set of odd positions and `e_i` the exponent of `cs` at position `i`, so `Re e_i = r`. The
  spherical list `sphList` consists of the even characters with complex exponents
  `e_i - [i ∈ A]` (`shiftExp`). Their real parts are `r - [i ∈ A]`; the imaginary parts
  `Im e_i` are arbitrary and play no role. `IsRealLanglandsOrdered` only compares real parts.
  Since `A` is a bottom segment, the real parts `r - [i ∈ A]` do not increase along the list.
  So the list is in Langlands order, and `RealSphericalCyclicStatement` applies to `sphVec`.

Weight-zero induction blocks.

* `blockChars x`: the characters of a block that is not a discrete-series block: `[x]` for a
  character, and `[sgn·|·|^t, |·|^t]` for an induction block of weight `0` and exponent `t`.
  (On a discrete-series block it is not used.)
* `realBlockExpand_eq`, `flatMap_expand_eq`: on blocks and lists with
  `¬ IsRealDiscreteSeriesBlock` the Library's `realBlockExpand` is `blockChars`.
* `exponent_re_of_mem_blockChars`: these characters keep the real exponent of the block.
* `sortParity cs`: the even characters of `cs`, then the odd ones. `sortParity_perm` and
  `pairwise_sortParity` show that it is a permutation with weakly increasing parities.

Main theorem.

* `hasScalarCommutant_of_nondiscrete (hS : RealSphericalCyclicStatement) n ds hrank htied hnd`:
  assume `realRank ds = n`, all real block exponents of `ds` are equal (`htied`), and no block
  is a discrete-series block (`hnd : ∀ x ∈ ds, ¬ IsRealDiscreteSeriesBlock x`). Then
  `HasScalarCommutant n ds`. Proof:
  1. The Library's `realStandardModule_append_flatMap_expand` shows that the standard module of
     `ds` equals that of the character list `ds.flatMap blockChars`.
  2. `sortParity` of that list satisfies `hasScalarCommutant_sorted`.
  3. `hasScalarCommutant_perm` moves the result back to the unsorted character list.
  4. `hasScalarCommutant_of_twoWay`, with identity maps between the equal modules, moves it to
     `ds`.
* `realTiedNondiscreteReduction : RealTiedNondiscreteReductionStatement`: given
  `RealSphericalCyclicStatement`, the hypotheses of `RealTiedNondiscreteScalarCommutantStatement`
  are exactly those of `hasScalarCommutant_of_nondiscrete`.

Use. With a proof of `RealSphericalCyclicStatement` this gives
`RealTiedNondiscreteScalarCommutantStatement`, and with a proof of
`RealTiedDiscreteScalarCommutantStatement` the Library theorem
`realTemperedScalarCommutant_of_cases` then gives the target of Task 7626.
