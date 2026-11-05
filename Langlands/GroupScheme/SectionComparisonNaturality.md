# Naturality of group-scheme pullback along a section

For arbitrary schemes `S`, `S'`, a map `b : S' ⟶ S`, a section `a : S ⟶ S'`
and the equation `a ≫ b = 𝟙 S`, the existing `baseChangeSectionIso` is natural
in every actual group-scheme homomorphism. The declarations
`RadicalFieldTransport.sectionIso_naturality` and
`RadicalFieldTransport.sectionIso_inv_naturality` give the commuting squares
for its forward and inverse maps.

These are the unchanged general lemmas formerly in
`Rational/UnipotentRadicalGalois`. They use the actual pullback composition,
identity and equality comparisons, with no field or group-structure assumptions
beyond being group schemes. This shared placement supports both radical
transport and maximal-torus transport without importing either application.
