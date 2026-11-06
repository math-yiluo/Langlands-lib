# Normalized word representation of the actual enveloping algebra

Authors: Worker 1431 and Worker 1687. Worker 1431 implemented this representation
and independence adapter; Worker 1687 implemented the generic normalizer,
concrete reductions, coherence and normal-form identities used by it.

For a field `k : Type u`, a Lie algebra `L : Type v`, and a supplied basis
`b : Module.Basis (Fin n) k L`, this unit constructs a representation of Mathlib's
actual `UniversalEnvelopingAlgebra k L` and proves independence of the published
ordered monomials. The universes vary independently, and the proof retains every
field characteristic and the case `n = 0`. All normalization identities used here
are proved in `OrderedPBWNormalization`; none is a premise supplied by a caller.

`normalAction b x` inserts `x` on the left of a formal word polynomial and applies
`normalForm b`. Linearity of insertion and normalization makes this a linear map
from `L` into the endomorphism algebra of `WordModule k n`.
`normalAction_map_lie` checks its Lie law: in a composition of two such operators,
`normalForm_insert_normalForm` removes the inner normalizer. The proved identity
`normalForm_insert_pair` identifies the difference of the two compositions with
insertion of the actual Lie bracket followed by normalization. Thus `lieAction b`
is a genuine Lie algebra homomorphism into the associative endomorphism algebra
with its commutator bracket.

`envelopingAction b` applies `UniversalEnvelopingAlgebra.lift` to that Lie
homomorphism. This is an algebra homomorphism whose domain is Mathlib's actual
tensor-algebra quotient, with its actual bracket relations. Its value at a Lie
generator is the constructed normalized insertion operator; no identification
with an arbitrary free algebra is assumed.

`envelopingAction_basisWord` proves by word induction that acting on the empty
word's unit singleton with an evaluated basis word gives the normal form of that
word's unit singleton. The empty case uses that the empty word is nondecreasing
and hence fixed by normalization. The cons case uses multiplicativity of the
actual algebra action, its generator formula, removal of the inner normalizer,
and the explicit action of `prepend` on a singleton.

`coefficientMap b` is the linear map from the actual enveloping algebra obtained
by applying the action to the empty word. For every exponent vector `e`,
`coefficientMap_orderedPBWMonomial` shows that its value at the actual ascending
power product is `Finsupp.single (exponentWord e) 1`. This follows from the
published monomial's exponent-word evaluation and the fact that the exponent
word is nondecreasing, so its singleton is fixed by normalization.

`orderedPBWMonomial_linearIndependent` pulls back independence along this linear
map. The unit singletons in the free word module are linearly independent, and
`exponentWord_injective` shows that restricting them to exponent words preserves
independence. Independence of these images therefore proves independence of the
actual ordered monomials. Together with `orderedPBWMonomial_span` from
`OrderedPBWSpanning`, this supplies the two clauses of the target PBW statement;
assembly and exact-target proof submission are separate from this helper unit.

This is an internal derivation using the already formalized coherent word
normalizer, its elementary list helpers, and Mathlib's universal property. It
uses no additional literature assertion and introduces no PBW, injectivity,
normal-form, polynomial-comparison or characteristic hypothesis.
