# Half-power descent reduces finite-order character prescription

Authors: Worker 53 and Worker 1232.

This internal reduction combines the elementary lemmas with
half-power descent and the proved topology of idele-class power quotients.
Its intended source is Artin and Tate,
*Class Field Theory* (AMS Chelsea, 2009), Chapter IX, Section 1, Theorem 1,
printed pp.65–66 (one-based PDF pp.74–75), and Chapter X, Section 2,
printed pp.77–80 (one-based PDF pp.86–89). The registered source is
`artin-tate-2009-class-field-theory`, SHA-256
`af7ba934904a3c10012e6fd326cea493ffb6200d885d97583277bb45f935c3dd`.
The implemented proof uses finite-image separation in a profinite quotient.
It does not identify the product topology with the topology induced on its
image in the idele-class group.

`prescriptionFiniteQuotient_of_halfPower_and_profinite` assumes
`AlmostEverywherePowerHalfStatement` and
`IdeleClassPowerQuotientProfiniteStatement`, each at the same arbitrary field
universe as the conclusion. Fix a number field `K`, a finite set `S` of its
actual finite places, a positive `n`, and an open subgroup `U` of the actual
prescription product containing its `n`th powers. The finite-index hypothesis
on `U` from the conclusion's statement is retained, although the construction
does not need it.

The first arithmetic hypothesis and the actual-coordinate retraction prove
that the preimage of the `(2*n)`th powers of idele classes is contained in the
`n`th powers of the local product. The local product modulo its `(2*n)`th
powers is finite, by the finite-completion theorem and the whole infinite
factor calculation, including every real sign coordinate. The second
arithmetic hypothesis supplies Hausdorffness, compactness and total
disconnectedness of the actual idele-class quotient by `(2*n)`th powers.
The generic separation theorem then gives an open finite-index subgroup `N`
of the actual idele classes, containing all `(2*n)`th powers, with exact
preimage `U`. Bundling `N` as an open subgroup gives precisely
`PrescriptionFiniteQuotientStatement`.

`finiteOrderCharacterPrescription_of_halfPower_and_profinite` applies the
character assembly to this finite-quotient assertion. The imported assembly
constructs a continuous Hecke character killed by `2*n`, proves every selected
finite component identity, and proves the prescribed identity on the whole
infinite factor. The field universe and the quantifiers of the original
target are unchanged.

The final two theorems discharge the topology hypothesis using
`Langlands.Global.ideleClassPowerQuotientProfinite_proof.{u}` from
`Langlands.Global.Arithmetic.IdeleClassPowerQuotientProfiniteProof`.
That imported theorem proves the named proposition at every field universe,
with the actual quotient topology, using an open S-unit idele subgroup and
an open surjection with finite kernel. Its proof and provenance are documented
in the imported module's Markdown.

`prescriptionFiniteQuotient_of_halfPower` applies the first conditional theorem
to this topology proof. `finiteOrderCharacterPrescription_of_halfPower`
then applies the character assembly. Their sole remaining premise is
`AlmostEverywherePowerHalfStatement.{u}`. Half-power descent remains an
explicit arithmetic input, so this module does not yet discharge the
unconditional prescription theorem. The separate `CharacterPrescriptionProof`
module supplies the proved half-power theorem and completes that final assembly.
