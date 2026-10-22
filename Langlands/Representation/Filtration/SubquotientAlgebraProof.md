# Composition and Artinian transfer for actual smooth subquotients

The proof establishes the two clauses of `Langlands.SmoothSubquotientAlgebraTheorem` over the full independent field, group, and representation-carrier universes.

For transitivity, the outer subquotient is expressed by an injective/surjective presentation through a smooth representation `X`. The inner subquotient supplies an actual invariant subrepresentation `S` and an actual quotient by `Q`. The proof pulls `S` back along the surjection from `X`, producing an actual smooth subrepresentation of `X`. Restricting the surjection gives a surjection onto `S`. Composing this with the quotient by `Q` and the supplied isomorphism gives the required presentation of the inner subquotient in the original ambient object.

For Artinian transfer, the proof uses the same presentation criterion, converts both intertwiners to linear maps over the group algebra, and applies Artinian transfer first across the injection and then across the surjection. The closing theorem bundles the two results. No analytic representation-theoretic result is used.
