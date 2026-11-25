# Actual torus products from integral Cartan-component coordinates

For a supplied `RootComponentCoordinates M`, this internal module constructs
an actual product presentation of the full coordinate maximal torus over
every base scheme. The factors are the split tori indexed by the simple
indices in each Cartan component. Their inclusions and projections are
retained, with identity on the matching component and zero cross projections.

The proof first regroups the individual multiplicative groups by Cartan
component, using explicit maps between categorical finite products. It then
uses `D.characters` to identify the resulting full simple-index torus with
the original coordinate torus. The latter construction extends
`splitTorus.exponentHom` to an actual isomorphism for an integral equivalence
between two possibly different index types. Composition of the inverse
character maps proves the two group-scheme inverse identities.

This is internally derived from the Library's finite products and fixed
integer exponent torus maps. It supplies the integral torus part of the
component factorization route motivated by Conrad, *Reductive group schemes*
(2014), Proposition 6.4.4, pp.232–233. It does not identify these tori with
maximal tori of derived centralizers or assert a product presentation of the
ambient reductive group.
