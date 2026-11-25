# A field criterion for an away localization

Module `StacksFrontier.RingTheory.DiscreteValuationRing.Abhyankar.AwayLocalizationField`, an extract of the file of the same path of the Lean library AxiomMath/Stacks. The origin of the file and what the extract leaves out are given at the end of this page.

Inverting a generator of the maximal ideal can give a field even when the original local ring is allowed to have zero divisors. This criterion is used for reduced branches in the proof of Abhyankar’s lemma.

`IsDiscreteValuationRing.ReducedTensorLocalization.away_field_of_artinian` proves `IsField` for the localization of a commutative local ring R away from π. It assumes that π is a non-zero-divisor, that it generates the maximal ideal, and that the localization is Artinian and reduced.

An idempotent written as a/πⁿ gives a² = aπⁿ by injectivity of localization. Induction on n forces a to be zero or πⁿ, using divisibility by π for a nonunit and cancellation of its powers. Distinct maximal ideals in a nonzero Artinian ring give a nontrivial idempotent, so the localization is local. Reducedness then makes it a field.

Stacks Project, Tag 09EQ.

## Origin of the file

Extracted from the Lean library AxiomMath/Stacks (https://github.com/AxiomMath/Stacks), commit `c496df0d9beea9deaeabcea8492605f9a0a2313b`, file `StacksFrontier/RingTheory/DiscreteValuationRing/Abhyankar/AwayLocalizationField.lean`. That library is distributed under the Apache License, Version 2.0; its licence text is kept with the Library's licences.

Changes made in the extract:

- Every declaration of the source file is kept.
- The import lines are those that the kept text needs.
- The library's Lean options that differ from Lean's defaults are set at the top of the file (`autoImplicit false`, `maxSynthPendingDepth 3`).
