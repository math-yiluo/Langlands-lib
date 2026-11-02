# Noetherian vanishing for relations with finite effective covers

`FiniteCoveredRelationsVanishing B` asserts degree-one vanishing for every
finite coefficient coaction on every ring étale equivalence relation over
`B` admitting a `FiniteEffectiveCover`. All rings and modules have the same
arbitrary universe `u`.

`finiteCoveredRelationsVanishing_of_quotientCovers` proves this property
for a Noetherian ring, assuming that finite effective covering data exists
after quotienting by any invariant ideal. This closure premise is explicit
in this helper and is not a consequence of its induction argument.

The proof applies Noetherian quotient induction to the property of the
base ring, quantifying over the relation ring and covering data inside the
property. In the reduced nonzero case, the generic-support theorem gives
a nonzero invariant ideal reducing each finite coefficient coaction to
modules annihilated by that ideal. The induction hypothesis applies to
the quotient relation with the quotient covering data. The imported
support-induction theorem transfers its vanishing back to the original
module. It also handles the nonreduced case by nilradical power
dévissage and the zero-ring case directly.

`isAcyclic_of_finiteCoveredRelationsVanishing` specializes the ring
property to an actual cover, removes coefficient finiteness using finite
stable subcoaction exhaustion, and applies the existing cocycle criterion
for acyclicity. The source algebra is flat because it is étale.

Provenance is internal composition of the actual finite effective cover
construction by Worker 239 and the generic-support, quotient-induction,
exhaustion and cocycle-to-acyclicity results. The helper retains its explicit
quotient-cover premise. The final scheme theorem in
`EtaleEquivalenceRelationComodulesAcyclicProof` supplies that premise using
`FiniteEffectiveCover.quotient`. No affine-descent conclusion is assumed.
