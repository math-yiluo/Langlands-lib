# Pointwise étaleness from finite to arbitrary recognized pieces

`Langlands.Analytic.AffinoidAtlasPresentation.StrongHom.finitePiecesEtaleAllPieces`
proves the existing Library proposition
`FinitePiecesEtaleAllPiecesStatement.{u, v, w} K`. For an actual strong map
between saturated affinoid-atlas presentations, joint pointwise étaleness
on a finite neighborhood family of recognized target pieces implies the
corresponding condition over every recognized target piece.

The field, space and atlas-index universes remain independent. The only field
hypotheses are `NormedField K`, `IsUltrametricDist K` and `CompleteSpace K`.
The theorem retains arbitrary positive finite polyradii, trivially valued
ground fields and non-Hausdorff ambient analytic spaces. Its conclusion
includes all recognized inverse-image realizations and chart points required
by `HasAllPiecesAt`.

## Implemented proof

The theorem applies the published reduction
`finitePiecesEtaleAllPieces_of_flatness_tensor` and discharges both of its
premises with published proofs:

- `PresentedAffinoidAlgebra.Domain.flatness` proves algebraic flatness of the
  structural map of every full represented affinoid domain.
- `PresentedAffinoidAlgebra.AffinoidPushout.finiteTensorComparison` proves
  bijectivity of the canonical ordinary tensor comparison to the actual
  affinoid pushout when the first map is finite Banach.

For clarity, the reduction keeps the original finite open source and target
neighborhoods. It selects one finite-family target piece through the image
point. Given an arbitrary recognized target piece through that point, the
recognition net supplies a common subpiece inside both. The finite-over
certificate supplies its actual recognized inverse image. The nested
pullback comparison and pointwise étale transport preserve étaleness from
the selected piece to the common subpiece and reflect it to the arbitrary
piece. Reflection uses faithful flatness at the contracted prime and the
Kähler differential base-change comparisons. The actual chart restriction
equations identify the point in every supplied source realization.

Thus the full-domain flatness and tensor-comparison inputs are proved
dependencies of this theorem. They add no hypotheses to the named target.

## Provenance

This is the final assembly of the Library's derived finite-to-all transport
argument. The supporting proof and its rationale are in
`FinitePiecesEtaleAllPiecesReduction.md` and `RecognizedNestedEtale.md`;
the two algebraic inputs are explained in
`GeneralizedAffinoid/DomainFlatnessProof.md` and
`GeneralizedAffinoid/FiniteTensorComparison/Proof.md`.
The geometric source motivation is recorded in the unchanged target
`FinitePiecesEtaleAllPiecesStatement.md`. This assembly uses the implemented
common-subpiece and prime-local reflection route described above.
