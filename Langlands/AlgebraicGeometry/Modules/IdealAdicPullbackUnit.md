# Pullback units and ideal quotients

For `f : X → Spec R` and `i : Y → X`, assume the actual structure-ring
map of `i ≫ f` sends every element of an ideal `I` to zero. This module
constructs a canonical map `M/I M → i_* i^* M` for every actual module
sheaf `M` on `X`.

`app_scalar` is the compatibility of a base scalar with the actual map on
sections over any open. Its proof is the naturality of the structure-sheaf
map. Semilinearity of the actual pullback unit then shows that it kills
all local ideal generators. `pullbackUnitDesc` is its factorization through
the quotient from `IdealAdicQuotientDescent`, and
`projection_pullbackUnitDesc` identifies its composite with the quotient
projection with the original adjunction unit.

These are internal constructions using the actual structure-ring map,
module pushforward and pullback adjunction. No flatness, coherence or
properness hypothesis is required. This unit does not assert that the
descended map is an isomorphism; that requires further geometric hypotheses.
