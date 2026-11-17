# All standard rank-two word laws for powered target maps

This internal supporting statement assembles the common-power and
exceptional-power calculations into the full set of standard A2, B2 and G2
word relations for a root-datum isogeny of finite reduced root data.
Throughout, the coefficient ring `R` is commutative and the original
characteristic input is retained: for every target root index `j'`,
`f.rootFactor j' ≠ 1` implies `(p : R) = 0`. This is the hypothesis
`hchar` used to construct the actual additive root-power maps.

`StandardPoweredWordRelations` quantifies over every pair of distinct source
simple roots. At the A2 Cartan pattern it requires the standard singleton
formula, at B2 both formulas, and at G2 all five formulas. Every map is the
actual powered simple map or its Weyl-word conjugate.
This proposition is defined over any commutative ring with that
characteristic input.

The proving theorems `standardPoweredWordRelations_of_normalData` and
`targetWordRelations_powered_of_noCone` additionally assume that `R` is
local and the ambient target group scheme is affine over `Spec R`.
They assume a genuine normalized target family for the transported
source words and corresponding simple-root supports. The first theorem applies the complete
rank-two scaling classification to the corresponding target pair. For each
source Cartan pattern, either the target entries are unchanged, when the
common-power calculations apply, or the lengths are exchanged in B2 or G2,
when the characteristic-two or characteristic-three calculations apply.
These exceptional characteristics are derived from the original `hchar`
and the root-factor ratio.
Every other case contradicts the given source entries. This exhausts the
possible root factors without adding a further characteristic or
uniform-power restriction.

The final helper supplies `TargetWordRelations` for the powered family from
these standard laws and an explicit premise that nonopposite roots with no
root in their positive integral cone commute. Thus no-cone commutation and
common Weyl conjugation remain separate obligations for using the general
commutator-transfer reduction. No ambient homomorphism or final affine
isogeny theorem is asserted.
