# Total determinant twisting on full automorphic isomorphism classes

Author: Worker 2. This internal construction descends the actual image
twists from `OperatorDeterminantTwist` to the existing full-operator
isomorphism classes over an arbitrary number field `F : Type u`.
The coefficient field is complex. General operator classes permit every
natural rank; cuspidal classes retain their existing positive-rank index
and compact additive adele-quotient instance.

`HeckeCharacter.finiteOrderSubgroup` is the subgroup of the existing
continuous Hecke-character group defined by the existing finite-order
predicate. Its identity, multiplication, and inverse laws reuse the
proved closure of that predicate.

`OperatorRealization.determinantTwist_congr` shows that equivalent full
realizations have equivalent actual twists. The existing full twist
relation is invariant under full equivalence, the actual construction
satisfies that relation, and its published fixed-character target
uniqueness supplies the required full target equivalence.
`OperatorRealization.IsoClass.determinantTwist` therefore descends by
`Quotient.lift`, with no representative selection. Its representative
formula is definitional. The identity character gives the original
full class by the existing identity-relation criterion. Composing actual
twists satisfies the relation for the product character; target
uniqueness proves the multiplication law. The inverse law follows.
These laws construct an actual group action of finite-order Hecke
characters on the existing full-operator classes.

`CuspidalOperatorRealization.IsoClass.determinantTwist` similarly descends
the actual total twist preserving irreducibility and cuspidality.
Forgetting to full operator classes commutes with this construction.
The injective existing forgetting map transports the identity,
multiplication, and inverse laws, giving the corresponding group action
on full positive-rank cuspidal classes.

`PositiveRankCuspidalClass.determinantTwist` applies the same construction
at the retained rank index of a mixed positive-rank class. The index and
actual rank are unchanged, the fixed-rank inclusion commutes with twisting,
and the finite-order character group acts on this existing mixed-rank type.

`isFiniteOrderDeterminantTwist_determinantTwist` proves that every input
cuspidal class has its constructed target in the existing relation.
For a specified finite-order character,
`isFiniteOrderDeterminantTwist_iff_eq` identifies that relation with
equality to this total target, using the existing fixed-character target
uniqueness theorem. This supplies actual targets for a relation which
previously did not assert their existence.

The provenance is direct internal quotient descent and relation-law
arguments using the actual image construction, the existing full
equivalence quotients, `FiniteOrderDeterminantTwist`, and
`HeckeCharacterFiniteOrder`. No new original-literature identification
is claimed. No nonzero cuspidal class is asserted to exist, and no
injectivity of finite forgetting, central-character transport, or
weak-association compatibility is proved here.
