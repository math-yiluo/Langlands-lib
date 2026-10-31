# Detecting invertibility of base change of Čech perfect models

This internal module isolates the geometric part of the perfect-model
base-change argument. All schemes, rings and complexes lie in an arbitrary
common universe. It considers a Cartesian square over spectra, a separated
morphism to the original affine base, a line bundle, a finite ordered affine
cover, and a chain map from an integer-indexed complex to the integer extension
of the line bundle's alternating Čech complex. The ring homomorphism is
arbitrary.

`quasiIso_cechBaseChangeCochainMap_iff` identifies the quasi-isomorphism condition
on the specified Čech base-change chain map with the quasi-isomorphism condition
on ordinary scalar extension of the input chain map. The defining factorization
ends in `scalarCechIntegerCochainMap`, which is an isomorphism by the imported
Cartesian separated base-change result. Cancellation of this
quasi-isomorphism proves the equivalence. No perfectness of the source is
needed for this first criterion.

For a strictly perfect source, the existing
`perfectModelBaseChange_cechDerivedComparison` identifies the actual perfect-model
base change with the localization of the specified Čech base-change chain map,
followed by the canonical target Čech comparison. Separatedness is preserved
by the Cartesian square, and pullback preserves quasi-coherence of the line
bundle, so the target comparison is invertible. Cancelling it and using the
derived category's detection of quasi-isomorphisms gives
`isIso_perfectModelBaseChange_cechDerivedComparison_iff`.

`cechPerfectModelBaseChangeIso` packages the resulting isomorphism when ordinary
scalar extension of the given chain map is a quasi-isomorphism. Its forward
map is exactly the previously specified `perfectModelBaseChange` of
`Q.map v` followed by the named source Čech comparison, as recorded by
`cechPerfectModelBaseChangeIso_hom`.

These constructions and proofs are internal consequences of the imported
actual maps and their compatibility. They do not assert that ordinary scalar
extension preserves every quasi-isomorphism, nor that any perfect
representative exists. Flatness and boundedness can supply the remaining
algebraic hypothesis in applications, but neither is an extra premise of the
criteria proved here.
