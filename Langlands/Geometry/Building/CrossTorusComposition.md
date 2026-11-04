# Identity and composition for actual apartment transport

This internal compatibility construction extends `CrossTorusApartmentComparison`.
It works over an arbitrary field with actual commutative group schemes, ambient
group schemes, and supplied commuting transport squares. No conjugacy-existence
hypothesis is needed to state the identities for those supplied squares.

The composite square uses the original isomorphisms in their given order. Full
root-function families transport by inverse precomposition on both the character
and rational-point indices. Identity transport fixes every family; transporting
successively along two pairs of isomorphisms equals transporting along their
composites. The implemented proofs evaluate at every character and point and use
associativity of the original morphisms.

Real cocharacter transport respects identity and composition, proved on elementary
tensors and sums. For affine ambient groups, quotient induction gives the same
identities for the original reduced translation spaces, with the common root
kernels and actual quotient derivatives retained.

For monomorphic embeddings and supplied `KPApartmentData`, identity and composition
hold for the entire data, including their full compatible valuation orbit. The
proofs identify carriers as images under the full-family maps; all remaining data
fields are propositions. The arbitrary scalar normalization function is unchanged.

`KPApartmentData.apartmentTransportComposition` compares the apartment obtained by
two successive transports with the apartment obtained by their composite square.
It retains every full valuation family and has identity derivative on the common
target reduced translation space. Composing the two actual affine point transports
with this comparison equals the direct actual affine transport. The analogous
`apartmentTransportIdentity` compares identity-transported data with the original
data, also retains families and has identity derivative; identity transport followed
by this comparison is the original apartment's identity affine map.

These are intrinsic identities of the published transport constructions. They do
not construct conjugating points, choose apartment classes over all maximal split
tori, prove apartment intersections or full A2, or establish general building
existence or descent. The provenance is internal: the morphism associativity,
tensor and quotient computations, carrier extensionality and the existing
identity-on-families affine comparison are the implemented route, rather than a
translation of a separately cited literature theorem.
