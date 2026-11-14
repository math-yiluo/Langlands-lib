# Extended affine roots for integer-valued building data

This internal helper extends the published integer-valued affine root result to
the extended affine roots of the same supplied data. It retains the actual
field, explicit valuation, group, torus, apartment and normalizer action. The
root-system conclusion assumes the same order-one unit as the published ordinary
root-system theorem.

`extendedAffineRootCoroot` chooses a coroot of an extended affine root from
the proved opposite-pair existence theorem. Its specification
`isCoroot_extendedAffineRootCoroot` says it is a coroot for the same actual
extended affine-root set; no order-one unit is needed for this construction.

The proof reuses the published normalizer preservation of extended roots and
the actual opposite-pair reflection. This gives extended-root coroots. V0 gives
the derivative equality with the actual relative roots; their finite spanning
set and coroot uniqueness give integral pairings for every coroot. The existing
integer-valued denominator estimate gives bounded finiteness, and the published
coroot translation supplies infinite derivative fibres. These are precisely the
corrected affine-root-system axioms, including rank zero. The final lemma is
AS4, obtained from V4 and the absence of quadruple relative roots.

The provenance is an internal extension of the published
`ValuationAffineRootSystems` proof to `IntegerValuationBuildingData`, using the
already published integer-valued reflection, discreteness and infinitude
helpers. No topology or additional building axiom is supplied or asserted.
