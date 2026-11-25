# Integral closures after a finite extension of fraction fields

Module `StacksFrontier.RingTheory.DiscreteValuationRing.BaseChangeClosure`, an extract of the file of the same path of the Lean library AxiomMath/Stacks. The origin of the file and what the extract leaves out are given at the end of this page.

Let A → B be an extension of discrete valuation rings with fraction fields K ⊆ L, and K₁/K finite. Put L₁ = (L ⊗_K K₁)_red, A₁ the integral closure of A in K₁ and B₁ that of B in L₁. This file describes the structure of L₁, A₁ and B₁.

## Definitions

- `IsNonemptyFiniteProductOfFiniteFieldExtensions K R` and `IsNonemptyFiniteProductOfFiniteSeparableFieldExtensions K R`: R is K-isomorphic to a product of n > 0 finite (separable) field extensions of K.
- `IsFiniteProductOfDedekindDomains R` and `IsFiniteProductOfDiscreteValuationRings R`: R is isomorphic to a product of n > 0 Dedekind domains, respectively discrete valuation rings.

## Main result

`integralClosures_after_finite_fraction_field_extension` (Tag 09EM). L₁, A₁, B₁ enter through isomorphisms with the nilradical quotient and the integral closures, with compatibility conditions. Conclusions:

- L₁ is a nonempty finite product of finite field extensions of L; A₁ is Dedekind; B₁ is a finite product of Dedekind domains.
- For a uniformizer π of A, π is regular in B ⊗_A A₁, inverting it gives L ⊗_K K₁, and B ⊗_A A₁ → B₁ is integral, with kernel in the nilradical, surjective on spectra.
- Spec B₁ → Spec A₁ is surjective; A₁ has finitely many maximal ideals, at least one; over each lie finitely many maximal ideals of B₁, at least one.
- Every maximal ideal q of B₁ lies over a maximal ideal p of A₁; both localizations are discrete valuation rings, joined by an injective local homomorphism.
- A henselian or complete: A₁ is a discrete valuation ring. B henselian or complete: B₁ is a finite product of discrete valuation rings.
- K₁/K purely inseparable: A₁ and B₁ are discrete valuation rings.
- K₁/K separable: L ⊗_K K₁ is reduced, L₁ is a product of finite separable extensions, and A₁, B₁ are finite over A, B.
- A (or B) Nagata: A₁ (or B₁) is finite over it.

Also public: `isLocalization_away_of_ne_zero_of_not_isUnit` (a discrete valuation ring's fraction field is its localization away from any nonzero nonunit) and `finite_primeSpectrum_of_dimensionLEOne` (a domain of dimension at most one with finitely many maximal ideals has finite spectrum).
## Points to watch

- The four product predicates are this file's own; the two ring-product predicates also require at least one factor, and factors lie in fixed universes.
- The reduction is the quotient by the nilradical; L₁, A₁, B₁ are given up to isomorphisms supplied as hypotheses.
- The hypothesis `hfieldSquare` is unused; a comment calls it a consequence of the scalar towers.

## References

Tag 09EM. SGA 6, X 7.13.3, is cited for the private lemma on integral closures of henselian discrete valuation rings.

## Stacks Project tags

| Tag | Declaration | Note |
| --- | --- | --- |
| [09EM](https://stacks.math.columbia.edu/tag/09EM) | `integralClosures_after_finite_fraction_field_extension` |  |

## References to EGA and SGA

| Source | Place | Declaration | Note |
| --- | --- | --- | --- |
| SGA | 6 X 7.13.3 | `isDiscreteValuationRing_integralClosure_of_henselianLocalRing` |  |

## Origin of the file

Extracted from the Lean library AxiomMath/Stacks (https://github.com/AxiomMath/Stacks), commit `c496df0d9beea9deaeabcea8492605f9a0a2313b`, file `StacksFrontier/RingTheory/DiscreteValuationRing/BaseChangeClosure.lean`. That library is distributed under the Apache License, Version 2.0; its licence text is kept with the Library's licences.

Changes made in the extract:

- Every declaration of the source file is kept.
- The import lines are those that the kept text needs.
- The library's Lean options that differ from Lean's defaults are set at the top of the file (`autoImplicit false`, `maxSynthPendingDepth 3`).
- The import of the library's own attribute modules is replaced by `Mathlib.Tactic.CrossRefAttribute`.
- One reference to EGA or SGA, written in the source as an attribute of that library, is taken out of the Lean text and listed above.
