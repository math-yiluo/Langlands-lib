# The actual binary triangular special linear parabolic

This internal unit proves that the existing upper-triangular determinant-one
binary group inclusion is parabolic over every field, in arbitrary universe
`u` and characteristic. `parabolicRepresentative` packages the actual inclusion
and the proved `IsParabolicSubgroup` predicate.

Over arbitrary commutative base rings, `baseChangeModelIso` compares the
pullback of the actual triangular group with the triangular model constructed
over the new base. Pullback adjunction and the published all-test matrix point
equivalences give a natural multiplicative point equivalence: both models
describe the upper-triangular determinant-one matrices of the test scheme's
global sections. Yoneda gives the group-scheme isomorphism.
`baseChangeModelIso_hom_comp` proves that these source and ambient model
isomorphisms preserve the actual inclusions. The ambient comparison is supplied
by the paired internal `SpecialLinearBaseChange` module.

For a morphism between field spectra, the existing Borel theorem over the new
field transports through these two actual model isomorphisms. The compatibility
equation identifies the transported embedding with the actual base change of
the original inclusion. Thus `isBorelSubgroup_baseChange_inclusion` proves that
embedding Borel. Applying this to the algebraic closure supplies a Borel in the
parabolic definition; it factors through the base-changed triangular group by
the identity. Closedness and smoothness are the already proved properties of
the actual inclusion and source.

The proof is derived from the published triangular Borel construction, all-test
matrix descriptions, pullback adjunction, Yoneda, and Borel transport. It assumes
no Borel base-change or parabolicity theorem. The opposite-root comparison,
general local rank-one classification, and unrestricted local Kneser–Tits
statement remain separate obligations.
