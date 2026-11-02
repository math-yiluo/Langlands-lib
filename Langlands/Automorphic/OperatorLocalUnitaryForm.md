# Positive forms on actual whole-carrier local restrictions

For an actual automorphic operator realization over any number field and
natural matrix rank, this internal construction restricts a supplied
whole-operator positive form to the actual group at each finite place.
The number field has arbitrary universe and coefficients are complex.

`OperatorRealization.UnitaryForm.localForm` uses the published generic
`InvariantPositiveForm.comp` on the actual continuous one-place inclusion
into the finite adelic general linear group. The representation is the
existing `localRepresentation`, on the original actual form carrier.
Its positive Hermitian core is precisely the supplied finite invariant
core. Local invariance is the original finite invariance at the image of
the local group element. `localForm_inner` records the unchanged values.
No additional local positivity or invariance premise is supplied.

`localImageForm` transfers this same form to the existing whole-carrier
local restriction of the faithful finite invariant image in actual forms.
It uses `InvariantPositiveForm.ofEquiv` and the inverse of the actual
`localFormEquiv`. Thus its value on arbitrary image vectors is the original
form on their inverse images. `localImageForm_inner_apply` proves that
this actual image equivalence is an isometry for the chosen forms.

`toSubquotientLocalForm` similarly transfers the form through the inverse
of `toSubquotientLocalEquiv`. This is the published equivalence onto the
actual module quotient with zero denominator. The inverse-coordinate
formula is proved, and `toSubquotientLocalForm_inner_projection` states
that the actual canonical projection preserves the chosen form exactly.
This construction uses the genuine zero-denominator equivalence.

The three results in `OperatorRealization.IsUnitarizable` pass these
constructors through the existing existence predicate. They prove generic
unitarizability for the actual whole-carrier local action, its faithful
local form image and its zero-denominator quotient presentation.

The provenance is internal. The local group inclusion, whole-carrier
restriction, actual finite form image, module quotient, canonical projection
and their local equivalences are existing constructions. The published
generic positive-form restriction and injective transport establish all
positivity and invariance obligations. The isometry proofs use the actual
equivalences' inverse identities. No new original-literature identification
is asserted.

These statements concern restrictions on the whole carrier. They do not
choose local tensor factors, assert local irreducibility or admissibility,
or supply a restricted tensor decomposition. A supplied whole-operator
positive form is an explicit input; no general existence, converse local
criterion or descent to a quotient with nonzero denominator is asserted.
There is no topology on representation carriers, continuous-form claim,
Hilbert globalization, invariant integral or spectral occurrence result.
No CM-field, character or compact additive adele quotient is needed.
