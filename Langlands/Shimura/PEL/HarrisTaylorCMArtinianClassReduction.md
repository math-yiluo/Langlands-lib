# Pointed lifting of normalized Harris classes

`NormalizedPolarizedActionLiftsAlong` asks for a lift of each positive polarized
action satisfying the normalized determinant and numerical conditions along a
map of quasi-separated schemes over the CM test base field `F`. The lifted
action satisfies the two conditions on the upper base. Its reduction is
identified with the original action by an equivariant rational isomorphism with
polarization multiplier one, as expressed by
`PositivePolarizedActionIsometricReduction`.

`classBaseChange_surjective_of_normalizedPolarizedActionLifts` proves
surjectivity of the existing pointed normalized class pullback at each Harris
level, given such lifts and surjectivity of the pointed monodromy map. It chooses
a lower class representative and transports an adelic frame of that
representative back along the rational isomorphism and base change. This
supplies the frame existence used to form the actual changed positive action.
The polarization comparison for its chosen dual data induces a level
equivalence. The pointed level pullback lifts the corresponding fixed orbit to
the upper action. The existing class equality criterion identifies the
restriction of the resulting upper class with the original lower class.

This is an internal reduction for the Artinian lifting criterion. It combines
the Library's polarized comparison, fixed-orbit surjectivity, and normalized
class equality.
