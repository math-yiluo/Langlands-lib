# Injective germ maps on reduced schemes

Module `StacksFrontier.AlgebraicGeometry.Morphisms.Valuative.GermInjective`, an extract of the file of the same path of the Lean library AxiomMath/Stacks. The origin of the file and what the extract leaves out are given at the end of this page.

On a reduced scheme with finitely many irreducible components, each point admits an affine neighbourhood whose sections inject into the local ring at the point.

`AlgebraicGeometry.Scheme.isGermInjective_of_isReduced_of_finite_irreducibleComponents` gives Mathlib’s `Scheme.IsGermInjective` under precisely these hypotheses. The lemma `finite_irreducibleComponents_of_isOpenEmbedding` gives the finiteness condition on any open chart by realizing its components as preimages of components of the ambient space.

On an affine chart, the proof uses the correspondence between irreducible components and minimal primes. For a prime `p` in the reduced coordinate ring, the localization lemma `exists_injective_localizationAwayToAtPrime_of_isReduced_finite_minimalPrimes` supplies a principal open about `p` whose sections inject into the localization at `p`. The affine cover then gives the result for the scheme.

Reference is Tag 0BX3.

## Origin of the file

Extracted from the Lean library AxiomMath/Stacks (https://github.com/AxiomMath/Stacks), commit `c496df0d9beea9deaeabcea8492605f9a0a2313b`, file `StacksFrontier/AlgebraicGeometry/Morphisms/Valuative/GermInjective.lean`. That library is distributed under the Apache License, Version 2.0; its licence text is kept with the Library's licences.

Changes made in the extract:

- Every declaration of the source file is kept.
- The import lines are those that the kept text needs.
- The library's Lean options that differ from Lean's defaults are set at the top of the file (`autoImplicit false`, `maxSynthPendingDepth 3`).
