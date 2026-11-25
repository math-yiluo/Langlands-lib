# The universal property of normalization

Module `StacksFrontier.AlgebraicGeometry.NormalizationBaseChange.UniversalProperty`, an extract of the file of the same path of the Lean library AxiomMath/Stacks. The origin of the file and what the extract leaves out are given at the end of this page.

A morphism from a normal scheme lifts uniquely to the normalization of its target if it sends
the generic points of irreducible components to generic points of irreducible components.
The file obtains this property from a unique extension of ring maps on affine charts.

## Ring and scheme statements

- `IsNormalRing.liftIntegralClosureFractionRing` extends a ring map A → B to the
  integral closure of A in its total ring of fractions, given that B is normal and the
  map preserves non-zerodivisors. `IsNormalRing.liftIntegralClosureFractionRing_unique`
  gives uniqueness among extensions to B.
- `mem_nonZeroDivisors_iff_forall_notMem_minimalPrimes` characterizes non-zerodivisors
  of a reduced ring by avoidance of all minimal primes. A companion lemma shows that
  minimal-prime contraction implies preservation of non-zerodivisors when B is reduced.
- `Scheme.exists_normalizationScheme_iso_reduction` identifies the normalizations of X and
  its reduction by an isomorphism over X.
- `Scheme.existsUnique_lift_normalization` gives the unique g from a normal Z to the
  normalization of X whose composite with the normalization morphism is the given
  f : Z ⟶ X. Both scheme theorems assume finitely many irreducible components in every
  quasi-compact open of X.

The induced map of total rings of fractions sends integral elements into B by normality.
Clearing a non-zerodivisor denominator gives uniqueness. The scheme proof factors through
the reduction of X, applies this ring argument on affine charts using the generic-point
condition as minimal-prime contraction, and glues by uniqueness. The comparison with the
reduction uses the relative normalization property after identifying the generic-point
residue spectra.

The universal property is part (4) of Tag 035Q. Its hypothesis `hgeneric` quantifies over
every generic point of an irreducible component of Z and requires its image to be a
generic point of an irreducible component of X.

Other references are Tag 034M, Tag 0356, Tag 035I, Tag 035O, and Tag 035P. The ring
integral-closedness lemma refers to EGA IV 6.14.1.1(i). The lifting theorem is listed as
a special case of EGA II 6.3.9 and EGA IV 8.12.11.

## Stacks Project tags

| Tag | Declaration | Note |
| --- | --- | --- |
| [035Q](https://stacks.math.columbia.edu/tag/035Q) | `existsUnique_lift_normalization` | normalization_universal_property |

## References to EGA and SGA

| Source | Place | Declaration | Note |
| --- | --- | --- | --- |
| EGA | IV 6.14.1.1 | `IsNormalRing.exists_algebraMap_eq_of_isIntegral` | (i) |
| EGA | II 6.3.9 | `existsUnique_lift_normalization` | special case |
| EGA | IV 8.12.11 | `existsUnique_lift_normalization` | special case |

## Origin of the file

Extracted from the Lean library AxiomMath/Stacks (https://github.com/AxiomMath/Stacks), commit `c496df0d9beea9deaeabcea8492605f9a0a2313b`, file `StacksFrontier/AlgebraicGeometry/NormalizationBaseChange/UniversalProperty.lean`. That library is distributed under the Apache License, Version 2.0; its licence text is kept with the Library's licences.

Changes made in the extract:

- Every declaration of the source file is kept.
- The import lines are those that the kept text needs.
- The library's Lean options that differ from Lean's defaults are set at the top of the file (`autoImplicit false`, `maxSynthPendingDepth 3`).
- The import of the library's own attribute modules is replaced by `Mathlib.Tactic.CrossRefAttribute`.
- 3 references to EGA and SGA, written in the source as attributes of that library, are taken out of the Lean text and listed above.
