# Smooth loci under flat base change

Module `StacksFrontier.RingTheory.Smooth.LocusBaseChange`, an extract of the file of the same path of the Lean library AxiomMath/Stacks. The origin of the file and what the extract leaves out are given at the end of this page.

For a finitely presented algebra, the smooth locus pulls back along a flat change of base. Over a field this gives a pointwise criterion for any extension of scalars to a commutative algebra.

## Results

- `Algebra.smoothLocus_comap_of_isPushout` takes R → S of finite presentation, R → R′ flat, and a base change S′ specified by `Algebra.IsPushout`. The inverse image of the smooth locus of S over R under Spec S′ → Spec S equals the smooth locus of S′ over R′.
- `Algebra.isSmoothAt_iff_isSmoothAt_of_isPushout` takes a field k, a finite type k-algebra S, and its base change S′ to a commutative k-algebra K. For primes q of S and q′ of S′ with q′ lying over q, S is smooth over k at q exactly when S′ is smooth over K at q′. The general flat pointwise statement is `Stacks.Smooth.FieldExtensionInvariance.isSmoothAt_iff_isSmoothAt_of_isPushout`.

The locus proof uses flat base change for first cotangent homology and base change for Kähler differentials. At each localized flat local map, faithful flatness reflects vanishing of homology and descends flatness of the finitely presented module of differentials, which is then free over the local ring. The pointwise result evaluates the locus equality at q′. Over the field k, K is flat and the finite type algebra S is finitely presented.

The equality uses flatness of R′ over R. For arbitrary base change, the preimage of the original smooth locus is contained in the new smooth locus. In the field-base statement K is allowed to be any commutative k-algebra. The loci use formal smoothness of prime localizations, which agrees with smoothness on a principal neighbourhood for these finitely presented algebras.

## References

Tag 00TG gives the locus equality and Tag 02UQ the field-base application. Tag 07BU gives the smoothness criterion and Tag 00S4 the cotangent comparison. The other references include Tag 00HR and Tag 00O1, EGA IV 17.7.2, SGA 1 II 4.13, and SGA 1 VIII 1.11.

## Stacks Project tags

| Tag | Declaration | Note |
| --- | --- | --- |
| [00TG](https://stacks.math.columbia.edu/tag/00TG) | `Algebra.smoothLocus_comap_of_isPushout` | The base change is the abstract one, `Algebra.IsPushout R S R' S'`, and the two smooth loci are Mathlib's `Algebra.smoothLocus`, which for a finitely presented algebra is the source's set of primes at which the map is smooth (Definition 00TB, via Lemma 07BU). The equality is oriented as `f⁻¹(U) = V`, as in `Algebra.smoothLocus_comap_of_isLocalization`. See the module docstring. |
| [02UQ](https://stacks.math.columbia.edu/tag/02UQ) | `Algebra.isSmoothAt_iff_isSmoothAt_of_isPushout` | The source takes `K/k` a field extension; `K` is here an arbitrary commutative `k`-algebra, since only flatness of `k → K` is used and that is automatic over a field. The base change is the abstract one, `Algebra.IsPushout k S K S'`, the prime correspondence is `Ideal.LiesOver`, and smoothness at a prime is Mathlib's `Algebra.IsSmoothAt`, which for a finite type algebra over a field is the source's Definition 00TB. See the module docstring. |

## References to EGA and SGA

| Source | Place | Declaration | Note |
| --- | --- | --- | --- |
| SGA | 1 VIII 1.11 | `free_of_free_baseChange` | special case |
| EGA | IV 17.7.2 | `solution` | (ii), affine case |
| SGA | 1 II 4.13 | `Algebra.smoothLocus_comap_of_isPushout` | affine case |
| EGA | IV 17.7.2 | `Algebra.smoothLocus_comap_of_isPushout` | (ii), affine case |
| EGA | IV 17.7.2 | `isSmoothAt_iff_isSmoothAt_of_isPushout` | (ii), affine case |

## Origin of the file

Extracted from the Lean library AxiomMath/Stacks (https://github.com/AxiomMath/Stacks), commit `c496df0d9beea9deaeabcea8492605f9a0a2313b`, file `StacksFrontier/RingTheory/Smooth/LocusBaseChange.lean`. That library is distributed under the Apache License, Version 2.0; its licence text is kept with the Library's licences.

Changes made in the extract:

- Every declaration of the source file is kept.
- The import lines are those that the kept text needs.
- The library's Lean options that differ from Lean's defaults are set at the top of the file (`autoImplicit false`, `maxSynthPendingDepth 3`).
- The import of the library's own attribute modules is replaced by `Mathlib.Tactic.CrossRefAttribute`.
- 5 references to EGA and SGA, written in the source as attributes of that library, are taken out of the Lean text and listed above.
