# The self-stabilizer of a tensor with distinct cuspidal factors

Author: Worker 495.

The theorem
`Langlands.CuspidalSupport.glDistinctCuspidalTensorStabilizer.{uF,uV} F T`
proves exactly the published proposition
`Langlands.CuspidalSupport.GLDistinctCuspidalTensorStabilizerStatement.{uF,uV} F T`
from `Langlands.Representation.CuspidalSupport.DistinctTensorStabilizerStatement`.
Its outer telescope is `{p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p)
(T : F.TopologicalData)`, with no additional assumptions.
This is an internal prerequisite for segment constituent existence; it
makes no assertion about induced heads or socles.

The theorem `Langlands.CuspidalSupport.distinctCuspidalTensorStabilizer_count`
works for arbitrary primes, supplied p-adic fields and their supplied
topological data. Field and representation-carrier universes remain
independent. For every block shape `B`, take actual supercuspidal factors
`A i` of ranks `B.size i`. Assume the function sending `i` to the actual
cuspidal datum `⟨B.size i, B.positive i, (A i).isoClass⟩` is injective.
Then the actual set of minimal coordinate permutations associating their
external tensor product to itself has natural cardinality one.

The identity belongs to this set. The published `index_strictMono` proves
its minimality, and `conjugatesLevi_one` and `leviConjugation_one` identify
its action on the Levi with the identity action. Thus the external tensor
is equivalent to its identity transport.

For any other member, restrict its actual tensor equivalence to the group
of one target block. The published `nonempty_equiv_of_factor_actions`
extracts an equivalence between that block factor and the source factor
pulled back along `factorHom`. Irreducibility of this pullback follows
from the surjectivity of `factorHom`. The actual matrix-entry description
`factorHom_apply_entry` and `blockPositionEquiv` then allow
`cuspidalDatum_eq_of_equiv` to identify their cuspidal data. Injectivity
forces `blockMap B B w i = i` for every block.

The coordinate permutation therefore preserves every block and lies in
`blockWeyl B`. Its Weyl double coset is the identity double coset.
The published `weylDoubleCoset_injective` identifies its minimal
representative with the identity. Subtype equality removes the nested
proof fields, and `Nat.card_eq_one_iff_exists` gives the cardinality.
This works for unequal ranks and for repeated ranks with distinct
isomorphism classes. The empty block shape needs no special assumption:
the universal factor argument is vacuous and the same identity witness
and minimal-representative uniqueness apply.

The exact wrapper installs the supplied topology and applies the direct
cardinality theorem to the quantified shape, actual factors and injectivity
hypothesis. It introduces no extra theorem-valued premises.

The derivation is internal, using actual tensor factor extraction and
finite Weyl combinatorics. It requires no Jacquet filtration or count,
induction theorem, freeness, semisimplicity, or central-character input.
It does not construct segment constituents. A recursive audit of all 77
project modules in this proof's import closure found no missing module
or excluded higher classification input. The only classification modules
are the actual supercuspidal category and twists, segment definitions,
supercuspidal-support definitions, and algebraic constituent relations.
The other branches contain matrix blocks, local-field normalization,
finite tensor actions, smooth transfer, and the actual Weyl and
association laws. The Jacquet-induction statement imported by the
minimal-coset proof is an interface, and no proof of its Jacquet
filtration conclusion is used.

Thus the implemented argument remains directly and transitively
independent of individual segment head/socle existence, segment analytic
classification, generic segment-product uniqueness, special-head product
irreducibility, ordered head/socle existence, multisegment exhaustion,
coverage or conversion, tempered uniqueness, square-integrable
classification or exhaustion, and regular exhaustion.
