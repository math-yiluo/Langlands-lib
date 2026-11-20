# Finite-place transport for the Proposition 4.8 parity correction

`Langlands.Global.Harris.Proposition48PlaceNormTwistStatement` gives the
actual corrected component at any compatible place above `p`. It applies
to each of the two places of the full problem and to the auxiliary place
of the internal induction. `Langlands.Global.Harris.GeneralPositionAmbientTwistStatement`
transports the original general-position hypothesis using the ambient
Weil character obtained for the auxiliary place.

## Actual finite component

The range clause of `PlaceDatum.IsCompatible` gives the ring isomorphism
from the upper completion to `F'`. The other clause and the completion
tower identity make this isomorphism compatible with the supplied lower
isomorphism to `F`. The tower identity follows by equality of the
continuous maps on the dense global field. The private lemmas in
`HarrisProposition48ExactStabilizerParityInheritanceProof` give the
tower and norm computations for the auxiliary place, with a corrected
component already supplied. The present input constructs that component.

For continuity of the completion isomorphisms, use the normalized
integer orders at both ends, whose residue characteristic is `p`.
Choose a prime `ℓ` greater than `p` and the two orders of `p`. In
either field an element `x` is integral exactly when `1 + p x^ℓ`
has an `ℓ`th root. For integral `x`, the polynomial
`Y^ℓ − (1 + p x^ℓ)` has the simple residue root `1`.
For negative order of `x`, the order of `1 + p x^ℓ` is negative
and congruent to the order of `p` modulo `ℓ`, which rules out an
`ℓ`th power. The isomorphisms preserve this equation and therefore
the valuation rings, their maximal ideals, and the powers of those
ideals that define the topology.

Transport the corrected character's finite component through the
upper isomorphism. `HeckeCharacter.normComp_finiteComponent` identifies
this component with the old component multiplied by the base
component pulled back through the local unit norm. Use
`Algebra.norm_eq_of_equiv_equiv` to compare the norms under the
compatible isomorphisms. For the ambient Weil character, read the
transported lower character through `reciprocityUnits` at
`Correspondence.baseExtension` and `Correspondence.baseWeilEquiv`.
`LocalFactor.NonabelianSystem.DeligneHenniart.reciprocityUnits_weilInclusion`
identifies its restriction with the norm factor. Each place may give
a different ambient Weil character.

## General position

Keep the same prime cyclic tower. In each Mackey constituent,
conjugation leaves the ambient character unchanged, so conjugate
restriction commutes with multiplication by its restriction. Use
`induceTwistEquiv` for the resulting induction and
`isIrreducible_twist_iff` for the tensor product by a character.
This transports every irreducibility clause in
`GeneralPosition.IsInGeneralPosition`.

## Provenance

Harris describes the local data and general-position condition in
Definition 4.5 and Proposition 4.8, printed pp. 200–203
(`math_9611226v1.tex`, lines 1524–1674). The finite component and
twist comparisons here are derived from local norm reciprocity and
the character twist identity for the actual Mackey constituents.
[Harris 1998, registered source `harris-1998-local-langlands`](https://arxiv.org/abs/math/9611226)
