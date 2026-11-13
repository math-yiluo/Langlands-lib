# Homomorphisms and isomorphisms of formal group laws

`CommLaw.Hom G H` is a pointed power-series map whose compatibility with
addition is an equality of formal maps on two copies of the source
coordinates. There are identity and composition operations, with the
identity and associativity laws. `Hom.onPoints` constructs the induced
additive homomorphism by evaluation on substitutable power-series tuples;
it preserves identity and composition.

`CommLaw.Iso` is a pair of mutually inverse formal homomorphisms.
`Iso.onPoints` constructs the resulting additive equivalence on points.
For no target variables these are maps on the nilpotent tuples identified
in `SeriesPoint.nilpotentEquiv`.

This is derived infrastructure for the formal modules of Drinfeld,
*Coverings of p-adic symmetric regions* (1976), §1, printed p.108 and the
quasi-isogeny convention on p.109. Source ID
`drinfeld-1976-coverings-p-adic-symmetric-regions`, SHA256
`7dd09e1967f46c29195ec87a400e145a17374368fc3b9dd0a782b5b7bfc44e2f`.
The explicit power-series homomorphism, composition and evaluation API
is implementation content. This module treats coordinate laws, not
locally glued formal groups, and defines neither rational homomorphisms
nor quasi-isogenies yet.
