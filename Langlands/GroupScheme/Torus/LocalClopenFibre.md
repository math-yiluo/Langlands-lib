# Clopen immersion from a fibre over a larger residue field

This derived construction combines fpqc reflection over fields
with the published Noetherian local special-fibre immersion criterion.

For a Noetherian local ring `R`, let `R → K` be any field-valued map whose
kernel is the maximal ideal. If a homomorphism from a relatively
diagonalizable group to an affine finite-type group becomes an isomorphism
under this field base change, `clopen_of_field_fibre_isIso` makes the
original homomorphism an open and closed immersion. The field map factors
through the residue field. Its induced field extension is fpqc and detects
isomorphisms, so the canonical special fibre is an isomorphism. The
published diagonalizable-source criterion then applies. The field map is
not required to be surjective, and no completeness or Henselianity is
assumed.

The companion evaluation lemmas show that evaluation on an arbitrary test
scheme preserves open immersions and that being an isomorphism after
evaluation is equivalent to being an isomorphism after raw base change.
Both use the canonical isomorphisms identifying iterated and direct
pullbacks. Closed-immersion preservation is already published in
`HomScheme.isClosedImmersion_evaluate`.
