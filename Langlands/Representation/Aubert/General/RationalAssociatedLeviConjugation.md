# Actual associated-Levi conjugation adapter

This is an internal construction from the named shared structural proposition
`GroupScheme.StandardLeviConjugationStatement` and the published actual
root-sign comparison predicates. It does not prove any of those premises.

`relativeRootSubset_image_of_character_image` converts an image equality of
actual character subsets into the corresponding equality of their exact
`toRat` encodings in `relativeRootSpan`. These are encoded sets of roots,
not their linear spans. The proof uses the representative formula for
`relativeWeylAction`. Only the source subset's containment in the actual
relative roots is needed; no injectivity of rationalization is asserted.

`levi_map_conj_of_character_image` applies the first clause of the named
all-test structural proposition to `rootSet J` and `rootSet J'`. It evaluates
the resulting subgroup-functor equality at the identity test object.
The result is literal image equality of the rational-point Levis under
`x ↦ n x n⁻¹`.

`associatedLeviConjugation_of_standard` supplies the actual
`actualAssociatedLeviConjugation` predicate needed by the generic Jacquet
target. Here the Weyl quotient is the normalizer of the actual torus image
modulo its full centralizer, and the labels are actual simple characters.
The separate numerator and denominator comparisons preserve each normalizer
representative. The existing `rootSet_associatedSubset` theorem, under
`RootLengthComparison`, `PositiveSimpleReflectionComparison`,
`minimalityLengthCriterion` and `associatedSubsetLaws`, identifies the
associated subset with the actual character image `w_J⁻¹(J)`.
Applying `w_J` recovers `J`, and the previous lemma yields the image
equality for every normalizer lift of the specified longest element of
`D(J, ∅)`. No arbitrary relabeling or separate associated-Levi image
hypothesis replaces these steps.

`associatedLeviConjugationEquiv` then constructs the continuous group
equivalence from `L_J` to `L_(w_J⁻¹J)` given by `x ↦ n⁻¹ x n`.
Its inverse is forward conjugation. Pullback along this equivalence therefore
transports representations in the source's forward-conjugation convention.
The construction works for any topological group topology on these points;
the later rational-point target uses the canonical evaluation topology.

The group is connected reductive, the torus maximal split and the
cocharacter generic. All underlying constructions are over an arbitrary
field; no splitness of the ambient group, characteristic assumption or
nonempty simple-root hypothesis is imposed. Finiteness of the simple-root
type and actual Weyl quotient is explicit. Independence of subgroup images
from a lift does not imply elementwise equality or independence of induced
representation classes. This adapter asserts neither of those stronger
conclusions and proves no main Aubert identity.

Provenance is internal: the implementation composes published actual-root,
actual-quotient, subgroup-functor evaluation and conjugation constructions.
The general structural proof remains with its existing owner; the named
root-sign realization and representation-theoretic obligations remain with
their existing owners.
