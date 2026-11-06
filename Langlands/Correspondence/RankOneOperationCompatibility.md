# Twists and duals for the actual rank-one correspondence

This internal derivation proves the twist and smooth-dual compatibility of the
actual rank-one correspondence along an explicitly supplied reciprocity
candidate. The field, Weil-carrier and automorphic-carrier universes remain
independent. The following describes the implemented proof.

The certified Weil twist and dual descend to the existing genuine representation
quotient. Forgetting their certificates gives the published algebraic class
operations. For a class satisfying `IsRankOneWeilCharacter`, its representative
can therefore be twisted or dualized in that quotient. The published twist
equivalence transports its scalar model to the twisted representative; the
scalar characters multiply. The published contravariant algebraic dual
equivalence transports its dual scalar model to the dual representative.
`scalarCharacterDualEquiv` evaluates a complex-linear functional at one and
identifies the algebraic dual of a scalar character with the inverse scalar
character. This construction works for every group, without a topology.
These arguments prove
`IsRankOneWeilCharacter.twist` and `IsRankOneWeilCharacter.dual`.

On the automorphic side, `IsRankOneCharacter.characterTwist` takes actual
classes realizing the characters `η` and `χ * η`. Twisting the first
scalar-model equivalence and composing with the second one proves the existing
`IsCharacterTwist` relation for those two actual classes. The determinant
pullback respects character multiplication by definition.

Similarly, `IsRankOneCharacter.smoothDual` takes actual classes realizing `χ`
and `χ⁻¹`. The character composed with the GL₁ determinant is continuous for the
canonical topology and has open kernel by the published nonarchimedean
open-kernel theorem. That open subgroup fixes every algebraic dual functional,
so the scalar representation's smooth dual is its full algebraic dual.
The published smooth-part inclusion equivalence and smooth-contragredient
transport, followed by evaluation at one, identify it with the inverse scalar
character. Composing with the representatives' scalar-model equivalences proves
the existing `IsSmoothDual` relation. This compares actual smooth-functional
subspaces, without assuming general dual closure.

Every actual rank-one Weil class is a pulled-back continuous field character
along the supplied reciprocity candidate. The constructed
`rankOneReciprocityEquiv` realizes the same field character on its supercuspidal
image. Applying the preceding Weil lemmas and automorphic relations proves
`rankOneReciprocityEquiv_twist` and `rankOneReciprocityEquiv_dual`. Character
pullback respects multiplication and inversion by definition. The conclusions
use exactly the endpoint's certified Weil operations and existing
`IsSupercuspidalCharacterTwist` and `IsSupercuspidalSmoothDual` relations.

Finally, the proved characterization of `SupercuspidalRankOneCompatibility`
identifies the rank-one component of any such family with the constructed
bijection. Rewriting gives
`SupercuspidalRankOneCompatibility.twist_rankOne` and
`SupercuspidalRankOneCompatibility.dual_rankOne`: precisely the rank-one
specializations of the endpoint twist and dual conditions.

The provenance is internal scalar linear algebra and transport through the
existing actual class relations. No reciprocity candidate is constructed, and
no geometric-normalization premise is needed for these implications. No
higher-rank compatibility, pair-factor identity or closed all-field
correspondence theorem is asserted.
