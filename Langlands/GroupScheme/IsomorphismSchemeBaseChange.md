# Group-isomorphism schemes under change of base

This internal construction transports natural local group-isomorphism families and their actual representing schemes along arbitrary morphisms of base schemes. It is derived from the published all-test `LocalGroupIso` interface, `GroupIsomorphismScheme` and the multiplicative pullback adjunction `baseChangePointsEquiv`. No reductivity, field, flatness or finiteness hypothesis is required.

For `b : S' ⟶ S` and a parameter `U` over `S'`, `LocalGroupIso.baseChangeFamily` restricts a family on the underlying `S`-parameter to tests over `S'`, transporting source and target points by the pullback adjunction. Conversely, `fromBaseChangeFamily` equips an `S`-test with an `S'`-structure using its point of `U`, applies the family there, and forgets that extra structure. The intermediate constructions in `ChangeOfBase` record these induced tests and prove their point correspondences natural under every refinement.

The two inverse laws are proved on every test and every group point. They use naturality of the original family along the canonical isomorphism between an induced test and the original test. `baseChangeEquiv` packages the resulting equivalence of full local families; `baseChangeFamily_refine` proves compatibility with every refinement of the parameter.

For a supplied representing scheme `I`, `GroupIsomorphismScheme.baseChangePointsEquiv` composes the pullback adjunction for parameter points, the original classification bijection and the family equivalence. The new universal family is the old universal family refined along the adjunction counit and transported to the new base. `baseChangeUniversalIso_refine` identifies its refinements with the classification equivalence. Its bijectivity constructs `GroupIsomorphismScheme.baseChange`, whose parameter is exactly the categorical pullback of `I.parameter`.

Every test is an arbitrary relative scheme. These constructions preserve an existing representation and do not assert geometric existence of an isomorphism scheme.
