# Actual finite images of full CM operator realizations

This internal comparison derives from the actual image constructions in
`OperatorCMTransport` and `FiniteLocalCMTransport`, and the canonical finite
form-image equivalences in `OperatorRealization`. It introduces no new
literature-defined carrier.

Let `K : Type uK` be an actual CM number field in any universe and `n` any
natural rank. For each actual full operator realization `S`,
`complexConjFiniteEquiv` identifies its finite representation, precomposed
with the actual finite adelic CM group automorphism, with the finite
representation of its actual full CM image. `complexConjCompactEquiv`
does the same for the existing standard infinite compact and its actual CM
automorphism. Both underlying linear equivalences are exactly the existing
continuous complex-linear CM equivalence on the embedded full realization.
Their equivariance follows from the corresponding proved covariance
equations. Values in the fixed coefficient field `Complex` do not change.

`toFiniteRealization_complexConj` proves equality of actual embedded finite
form subspaces. Thus taking the finite form image of the full CM image
equals taking the CM image of the original finite form image. The proof
compares range witnesses: the inverse full CM equivalence supplies the
source witness, and the forward form-inclusion covariance supplies its
image equation. It does not merely compare representation classes.

`complexConjFiniteImageEquiv` is a genuine representation equivalence
between the actual finite images, with the original finite representation
pulled back by the same arithmetic group map. It is the inverse source
finite-image equivalence, followed by the full CM equivalence, followed by
the target finite-image equivalence. The application formula identifies
these maps on every original realized vector. The evaluation formula is
the original function evaluated at the CM-transformed argument.

Finally, `toLocal_toFiniteRealization_complexConj` combines the embedded
finite-image equality with the finite-to-local CM image equality at the
corresponding pulled-back prime ideal. This local restriction retains the
whole finite carrier. It is not a selected tensor-factor component.

All form and image topologies are the existing inherited compact-open
topologies. The new representation equivalences are algebraic equivalences
whose underlying maps come from the displayed continuous image maps.
No quotient compactness hypothesis is needed for this comparison. No
irreducibility of a finite restriction, occurrence, tensor factorization,
spectral existence, classification, contragredient identification or
conjugate self-duality is asserted.
