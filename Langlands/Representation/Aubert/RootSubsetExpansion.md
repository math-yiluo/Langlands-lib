# Root-subset expansion of the existing GL Aubert operator

Author: Worker 585.

This internal indexing construction reuses `BlockShape.cutEquiv`,
`BlockShape.uncuts_card`, and `Aubert.alternatingOperator_eq_sum`.
It leaves the existing actual normalized induction and Jacquet maps in every
summand. The construction has no additional representation-theoretic input.

For GL of rank `n`, label the adjacent-coordinate simple-root positions by
`Fin (n - 1)`: index `i` corresponds to the pair of coordinates `i` and
`i + 1`, or to the usual root `e_i - e_(i+1)` under zero-based indexing.
The positions inside a block are the Levi-root indices, whereas block
boundaries are omitted. `leviRootSubsetEquiv` sends a positive ordered block
shape to the complement of its interior cuts. Its inverse reconstructs the
block shape from the complement of the supplied subset. Complementation is
involutive and the existing cut map is an equivalence, which proves both
inverse laws.

`leviRootSubsetEquiv_card` identifies the cardinality of this subset with
`n - B.length`. `alternatingOperator_eq_rootSubset_sum` reindexes the existing
finite sum along this equivalence and uses the cardinality formula to identify
each sign. Its conclusion is equality of integer-linear endomorphisms of the
existing exact finite-length smooth GL Grothendieck group.

The theorem holds for every natural rank, over the existing complex
`PadicField.{uF}` models and the supplied field topology, with representation
carriers in `Type (max uF uV)`. At rank zero `Fin (0 - 1)` is empty, its
finite-subset type has one element, and the inverse equivalence selects the
empty block shape. The sign is therefore one. The theorem adds no
positive-rank hypothesis.

The normalized functors retain their existing conventions: induction uses
the positive half-modulus, and Jacquet restriction the inverse half-modulus.
All representation-theoretic prerequisites remain those of the unchanged
`AlternatingOperator` module and its actual K0 functor maps. This unit neither
reproves their finite-length or exactness properties nor asserts their
classification independence.

The root positions here are an explicit combinatorial convention. This
unit does not construct a general reductive datum or prove its relative-root
subgroups equal to the actual GL subgroups. It supplies the GL index and sign
conversion needed after those structural and normalized-functor comparisons.
In particular, the displayed sum is a formula for the existing GL operator;
it is not a separately defined general Aubert operator or a completed
general-to-GL operator comparison.
