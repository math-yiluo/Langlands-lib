# Arbitrary smooth determinant-character twists of actual supports

This internal construction generalizes the published real-power support transport to any field character with open kernel. It is local infrastructure for `Langlands.Global.PoleComparison.RelativeIsometryOperationStatement.{uF, uW, uP}`. It asserts transport of supplied support witnesses, without asserting existence of supports or any global automorphic construction. The field and representation-carrier universes are independent.

`PadicField.TopologicalData.CuspidalDatum.characterTwist` retains the positive rank and twists the actual supercuspidal class by the character composed with the determinant. Its kernel is open by continuity of the determinant, and it is trivial on the determinant kernel. Thus the published supercuspidal class twist applies.

`normalizedProductCharacterTwistIso` packages `normalizedProductDeterminantTwistEquiv` as an isomorphism of actual smooth representations. That published equivalence multiplies induced functions by the determinant character, and identifies twisting the normalized induction with normalized induction of the individually twisted factors.

`IsCuspidalConstituent.characterTwist` opens a supplied constituent witness and twists each actual supercuspidal representative. Their new isomorphism classes are exactly the transformed data; irreducibility follows from `SmoothRep.isIrreducible_twist_iff`. The published `SmoothRep.IsSubquotient.twist` transports the actual subquotient witness, and the product isomorphism places it in the required normalized induction. Finally `IsSupercuspidalSupport.characterTwist` transports the finite enumeration and computes the resulting multiset by `List.map_ofFn`.

All content is derived from published definitions and proved operations. Public inputs are `GeneralLinear.SupercuspidalRep.twist`, `GeneralLinear.SupercuspidalClass.twist`, `GeneralLinear.ker_determinant_le_ker_comp`, `PadicField.TopologicalData.normalizedProductDeterminantTwistEquiv`, `SmoothRep.isIrreducible_twist_iff`, `SmoothRep.IsSubquotient.twist` and `SmoothRep.IsSubquotient.of_iso_right`. No classification existence or uniqueness statement is used.

`CuspidalDatum.characterTwist` packages the existing `Langlands.Classification.cuspidalCharacterTwist` using a `SmoothCharacter`; the rank, class operation and actual action are unchanged.
