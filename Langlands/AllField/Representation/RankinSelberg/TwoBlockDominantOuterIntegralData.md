# All-field port of `Langlands.Representation.RankinSelberg.TwoBlockDominantOuterIntegralData`

`Langlands.AllField.Representation.RankinSelberg.TwoBlockDominantOuterIntegralData` is the all-field port of the Library module `Langlands.Representation.RankinSelberg.TwoBlockDominantOuterIntegralData`, which belongs to the Library's development over p-adic fields `F : PadicField p` (with bundled topological data `F.TopologicalData` where a topology is needed). In the port, `F` is an arbitrary field with instances `[TopologicalSpace F] [ValuativeRel F] [IsNonarchimedeanLocalField F]` (see the next paragraph). Nothing about the characteristic of `F` is assumed, so the port covers every nonarchimedean local field, including those of positive characteristic.

The port imports the original module, so the field-independent declarations of the original are available to it unchanged. It re-declares, under the same name with `Langlands.` replaced by `Langlands.AllField.` (declarations of the original namespace `Langlands.PadicField.TopologicalData` move to `Langlands.LocalFieldData`), the declarations that involve the field and that the Library's p-adic proofs of JPSS gamma-factor and L-factor multiplicativity (`Langlands.RankinSelberg.gammaMultiplicativity`, `Langlands.RankinSelberg.lFactorMultiplicativity`) use. Each re-declared declaration keeps the statement, and for a theorem the proof, of its original. Only the field binders and the canonical data of the original (see the next paragraph) change, and the `T`-API (residue cardinality, normalized absolute value, uniformizer and their lemmas) comes from `Langlands.LocalFieldData` and `Langlands.AllField.LocalField.Foundation`.

Where the original quantifies over a p-adic field with its canonical data (`∀ (p : ℕ) [Fact p.Prime] (F : PadicField p)` together with `F.canonicalTopologicalData` or the canonical topology), the port quantifies over a field `F` with instances `[TopologicalSpace F] [ValuativeRel F] [IsNonarchimedeanLocalField F]`, and where the original uses the canonical data the port uses the data `(⟨⟩ : LocalFieldData F)` assembled from these instances (definitionally `LocalFieldData.ofInstances F`). Its topology is the ambient topology of `F`.

Source: the original module `Langlands.Representation.RankinSelberg.TwoBlockDominantOuterIntegralData` in the Library. Its Markdown file gives the literature provenance of each statement.

## Contents

The module docstring of the port:

**Outer integrals for the strictly dominant rectangle kernel**

This helper retains arbitrary functions on the actual lower quotient. It uses
exactly the existing lower transport of each supplied standard quotient measure.
The actual rectangle-integrated kernel, norm profile and fiber predicate are
supplied by `TwoBlockDominantQuotientKernelData`.

## Imports from the port

- `Langlands.AllField.Representation.RankinSelberg.TwoBlockLowerFixedSliceMeasureTransport`

## Declarations

- `Langlands.AllField.RankinSelberg.TwoBlockDominantRectangular.integrable_lowerQuotientMeasure_iff` (theorem): Absolute integrability also transports in both directions, independently of
  any identity of totalized integral values.
- `Langlands.AllField.RankinSelberg.TwoBlockDominantRectangular.ae_lowerQuotientMeasure_iff` (theorem): Almost-everywhere fiber conditions transport for arbitrary predicates.
- `Langlands.AllField.RankinSelberg.TwoBlockDominantRectangular.OuterIntegrable` (def): Actual outer complex integrability, recorded as a condition, not inferred.
- `Langlands.AllField.RankinSelberg.TwoBlockDominantRectangular.NormProfileIntegrable` (def): Outer integrability of the supplied real norm profile.
- `Langlands.AllField.RankinSelberg.TwoBlockDominantRectangular.AbsoluteInput` (def): Conditions for an analytic successor: actual outer complex integrability,
  outer integrability of the real norm profile, and almost-everywhere actual fiber
  integrability. No clause is inferred from a totalized integral value.
- `Langlands.AllField.RankinSelberg.TwoBlockDominantRectangular.absoluteInput_standard_iff` (theorem): The full absolute-input condition written on the standard quotient.
- `Langlands.AllField.RankinSelberg.TwoBlockDominantRectangular.standardCompatible` (def): Compatibility for every supplied right-invariance certificate and every
  standard quotient measure, at the existing exact standard Haar normalizations.
- `Langlands.AllField.RankinSelberg.TwoBlockDominantRectangular.standardCompatible_sigmaFinite` (theorem): Every compatible supplied standard measure and its prescribed lower measure
  are sigma-finite. This selects no new measure or normalization.

Public declarations of the original that are not re-declared here: `Langlands.RankinSelberg.TwoBlockDominantRectangular.lowerQuotientMeasure_eq_map`, `Langlands.RankinSelberg.TwoBlockDominantRectangular.integral_lowerQuotientMeasure`, `Langlands.RankinSelberg.TwoBlockDominantRectangular.outerIntegral`, `Langlands.RankinSelberg.TwoBlockDominantRectangular.outerIntegral_eq`, `Langlands.RankinSelberg.TwoBlockDominantRectangular.outerIntegral_standard`. Each of them either does not involve the p-adic field, and is then available from the original module, or is not used by the two multiplicativity proofs.
