# Fibres of multivariable polynomial rings

Module `StacksFrontier.RingTheory.RegularLocalRing.MvPolynomialFiber`, an extract of the file of the same path of the Lean library AxiomMath/Stacks. The origin of the file and what the extract leaves out are given at the end of this page.

The fibre of the polynomial algebra R[xᵢ] over a prime 𝔭 of a commutative ring R is a polynomial ring over the residue field κ(𝔭).

- `Ideal.isDomain_fiber_mvPolynomial` and `Ideal.equidimensional_primeSpectrum_fiber_mvPolynomial` show that the fibre ring is an integral domain and its spectrum is equidimensional for any variable type.
- `Ideal.isRegularRing_fiber_mvPolynomial` gives regularity for a finite variable type ι, and `Ideal.ringKrullDim_fiber_mvPolynomial` gives Krull dimension `Nat.card ι`. At any prime of this fibre the localization is regular local by `Ideal.isRegularLocalRing_localization_fiber_mvPolynomial` and maximal Cohen–Macaulay over itself by `Ideal.isMaximalCohenMacaulay_localization_fiber_mvPolynomial`.
- `Ideal.isMaximalCohenMacaulay_and_equidimensional_and_ringKrullDim_fiber_mvPolynomial` bundles the local maximal Cohen–Macaulay property, equidimensionality and dimension n for variables indexed by `Fin n`. A separate bound gives dimension at most n for each local ring in this case.

The proofs transport the polynomial ring facts along `MvPolynomial.algebraTensorAlgEquiv`. The domain property gives irreducibility and hence equidimensionality, and regular local rings give the Cohen–Macaulay property.

The bundled theorem supplies the hypothesis `hfib` of the openness theorem for fibrewise exactness in the polynomial case. All statements allow an arbitrary commutative coefficient ring R.

Stacks Project Tag 00NQ for the regular local input, Tag 00RB for the fibre hypothesis, and Tag 00RC for the polynomial application. EGA 0, 17.3.7, for regularity over a field.

## References to EGA and SGA

| Source | Place | Declaration | Note |
| --- | --- | --- | --- |
| EGA | 0 17.3.7 | `isRegularRing_fiber_mvPolynomial` | coefficient ring a field |

## Origin of the file

Extracted from the Lean library AxiomMath/Stacks (https://github.com/AxiomMath/Stacks), commit `c496df0d9beea9deaeabcea8492605f9a0a2313b`, file `StacksFrontier/RingTheory/RegularLocalRing/MvPolynomialFiber.lean`. That library is distributed under the Apache License, Version 2.0; its licence text is kept with the Library's licences.

Changes made in the extract:

- Every declaration of the source file is kept.
- The import lines are those that the kept text needs.
- The library's Lean options that differ from Lean's defaults are set at the top of the file (`autoImplicit false`, `maxSynthPendingDepth 3`).
- The import of the library's own attribute modules is replaced by `Mathlib.Tactic.CrossRefAttribute`.
- One reference to EGA or SGA, written in the source as an attribute of that library, is taken out of the Lean text and listed above.
