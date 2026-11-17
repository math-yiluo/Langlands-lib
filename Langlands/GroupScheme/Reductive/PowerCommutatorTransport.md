# Common-power transport of actual commutator formulas

This internal derived module transports the literal `CommRel` formulas
when all maps are precomposed by the same supplied power homomorphism
`F : Ga R ⟶ Ga R`. The hypothesis on `F` is its actual point formula
`x ↦ x^q` on every scheme test. The module does not construct `F` or
assume its existence from an unspecified characteristic.

`sectionPowerRingHom` constructs the corresponding power ring
endomorphism on the global sections of every test scheme. Its
additivity and zero identity follow by applying the scalar coordinate
to the actual group-homomorphism identities for `F`. Its product and
unit identities are the ordinary power identities in a commutative
ring. Thus no reducedness, nontriviality, field or localness
hypothesis on `R` or the test scheme is required.

`powerCommTerms` precomposes every map in a list of actual commutator
terms by `F`, retaining its coefficient and its two exponents.
`CommRel.precompose_power` transfers a formula to these precomposed
maps when each scalar coefficient is fixed by the power on every
test. The proof evaluates the original formula at `x^q` and `y^q`.
Each new term evaluates to its old term at those arguments because
powers preserve products and commute with other natural powers.

`CommRel.precompose_power_of_int_coeff` supplies the coefficient
hypothesis automatically when every term coefficient is the image
of an integer. The constructed ring endomorphism fixes integer
scalars, so this covers universal integer-coefficient commutator
formulas, including negative constants.

The provenance is composition of the imported actual point formulas
and elementary ring and list identities. These results concern a
single common exponent and a supplied actual power homomorphism.
They do not handle distinct root factors, reindexing of root systems,
or the exceptional rank-two isogeny formulas.
