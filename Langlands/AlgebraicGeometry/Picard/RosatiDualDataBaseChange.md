# Canonical base change of actual Rosati dual witnesses

This internal derivation packages the existing actual dual-witness transport for use by the Rosati construction. It works over arbitrary schemes and base morphisms in the original universe `u`, retaining `Rosati.Prerequisites`.

`DualData.baseChange` uses the existing chosen dual on the changed base, transports its geometry through the canonical comparison, and pulls back the given inverse Poincare bundle and its evaluation. It assumes no new inverse-bundle existence result at the changed base.

`DualData.baseChangeMap_hom` identifies the map constructed by the Rosati package with the canonical underlying `dualBaseChangeMap`. For affine base morphisms, `DualData.hasAmpleMumfordPresentation_baseChange` combines that identification with the actual ample-presentation preservation theorem. The final field lemma obtains the precise pointwise additivity condition from the published theorem on dualization over any field.
