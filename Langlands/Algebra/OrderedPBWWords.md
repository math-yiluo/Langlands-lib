# Ordered words and exponent vectors for PBW

Author: Worker 1431.

This is internal combinatorial infrastructure for the ordered finite-basis PBW
proof. It introduces no normal-form or independence assumption.

`exponentWord e` expands an exponent vector `e : Fin n → ℕ` to the list
obtained by concatenating `e i` copies of each index `i` in ascending order.
`exponentWord_pairwise` proves that this list is nondecreasing: each block is
constant, and every index in an earlier block is less than every index in a
later block. `exponentWord_count` computes the count of index `i` as `e i`
using the finite sum of block counts. Thus `exponentWord_injective` recovers an
exponent vector by counting.

`pairwise_eq_exponentWord` proves that an ascending word is exactly the exponent
word of its counts. The proof uses equality of the counts to obtain a list
permutation, then the uniqueness of an ascending list in its permutation class.
`exponentWordEquiv` packages these two inverses as an equivalence between exponent
vectors and the subtype of nondecreasing words. This includes `n = 0`.

`exponentWord_product` maps the exponent word through the actual Lie-generator
map of Mathlib's `UniversalEnvelopingAlgebra` and takes its list product. Mapping
across the concatenation and multiplying each constant block proves that this is
exactly the published `orderedPBWMonomial b e`, with ascending factor order and
independently varying field and Lie-algebra universes.

`exists_adjacent_inversion` proves by list induction that a word that is not
nondecreasing has a decomposition `a ++ i :: j :: c` with `j < i`.
`shortlex_adjacent_swap` shows that replacing this pair by `j :: i` decreases
Mathlib's shortlex relation: the length stays fixed, and at the first changed
entry the index decreases. These two lemmas apply to any linearly ordered type.
They supply termination for later word-reordering arguments; they establish no
quotient-algebra independence or confluence themselves.

These are elementary derived facts about finite linear orders, list counts,
and products, written for this proof. The connection with the PBW source is the
published `Langlands.Algebra.OrderedPBWMonomials` construction imported here; no
additional literature assertion is used in this internal unit.
