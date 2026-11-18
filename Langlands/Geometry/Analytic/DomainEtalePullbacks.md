# Pullbacks along domains of étale spaces

`isPullback_domainPreimage_comp` restricts the first factor `A` of an
analytic pullback `P` to a domain `D`. The new pullback point is the
inverse-image domain of `D` in `P`. Its first projection is the restriction
of the old first projection, and its second projection is the inclusion
into `P` followed by the old second projection. The proof pastes the
literal domain preimage square with the original pullback square.

`domainEtalePullback` constructs a limiting cone over `f : A ⟶ X` and
`g : B ⟶ X` in the localized analytic category with independent field and
space universes and a common space and atlas-index universe. It uses an
explicit factorization of `f` through an analytic domain of an étale
space over `X`. It pulls back the étale space along `g`, restricts the
first factor to the given domain, and transports that square along the
isomorphism identifying `A` with the domain. The limit witness applies to
every object of the localized category.

The provenance is internal. The construction combines the published
localized étale pullback and domain preimage limit with pullback pasting
and invariance under isomorphism.
