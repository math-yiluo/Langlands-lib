# Rigidity of actual opposite-root restrictions over local rings

This internally derived module combines `LocalOppositeRootNormalization` and
`OppositePowerRigidity` to compare actual negative-root restrictions. Its proof
uses the normalization and all-test Gauss comparison implemented in those
modules. It does not claim the full isogeny torus-conjugacy theorem.

For an actual homomorphism `f`, `HasPowerFormula.scaleSource` changes the
coefficient `c` to `c*s^q` when the source coordinate is precomposed with
`scaleHom s`. The scalar `s` is arbitrary. `HasPowerFormula.scaleTarget` changes
the coefficient to `t⁻¹*c` when the target coordinate is precomposed with
`scaleHom t` for a unit `t`. Both are identities on every scheme test over
`Spec R`; they follow from the root-point scaling formula and ring arithmetic.

`opposite_maps_eq_of_normalizations` assumes the source and target negative
coordinates have been separately rescaled by units `s,t` to satisfy the Gauss
relations and target positive-coordinate separation. Two homomorphisms carry
the supplied source torus into the target torus and have the same positive
coefficient `c : Rˣ` and power degree `q > 0`. Their negative coordinates may
have arbitrary coefficients `d,d'`, with the same degree `q`. Rescaling changes
these to `t⁻¹*d*s^q` and `t⁻¹*d'*s^q`. The normalized comparison gives equality
after precomposition with `scaleHom s`; cancelling its scale isomorphism gives
equality of the original negative restrictions.

`LocalSplitCell.opposite_maps_eq_of_powerFormulas` supplies these normalization
premises for actual root parametrizations in reductive affine group schemes
over an arbitrary commutative local ring. The source and target have closed,
fibrewise maximal coordinate split tori, supplied fibrewise root data `P,Q`,
and chosen opposite root pairs for roots `a,b`. The two torus maps may differ.
With the four all-test power formulas, the shared positive unit coefficient,
and the common positive degree as above, the actual morphisms `xm` followed
by the two homomorphisms agree.

`LocalOppositeRootRigidityStatement` quantifies this conclusion over all the
preceding local-ring data in universe `u`. `localOppositeRootRigidity` proves it
by applying `opposite_maps_eq_of_powerFormulas`.

The construction independently normalizes the two actual opposite pairs using
`exists_unit_oppositeNormalization`, forgets the specified coroot middle
factors, and applies the preceding rescaling comparison. No reducedness
assumption on the local ring or unit assumption on either negative coefficient
is used. Construction of these power formulas for arbitrary isogenies, the
positive unit coefficient, positive-root comparison by torus conjugation and
assembly of the full rigidity theorem remain separate obligations.
