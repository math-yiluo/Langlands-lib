# The product topology on S-unit ideles

Author: Worker 107.

This internal construction identifies the Library's subgroup `sUnitIdeles K S`
with the product of the whole infinite idele factor, the full multiplicative
groups at finite places in `S`, and valuation-unit groups at finite places
outside `S`. It uses the actual units topology on the adele ring.

The assembly map builds both the value and inverse in the restricted-product
stage attached to the complement of the finite set `S`. Inclusion of that
stage is continuous. Reading coordinates is continuous in the actual idele
topology, and the two maps are inverse multiplicative maps. This gives the
continuous multiplicative equivalence `productEquiv`.

The subgroup is open because its elements are exactly those ideles for which
both the value and inverse are integral outside `S`. Each integrality condition
is an open restricted-product condition; their inverse images under the value
and inverse maps are open.

These are derived topological adapters for the S-unit route to the
positive-power idele-class quotient theorem. The arithmetic and topological
context is Artin and Tate, *Class Field Theory* (AMS Chelsea, 2009), Chapter X,
Section 2, printed pp.77–79 (one-based PDF pp.86–88), registered as
`artin-tate-2009-class-field-theory`. The explicit product equivalence here is
an internal implementation rather than a separately quoted assertion of that
source. It asserts no compactness or power-quotient theorem.
