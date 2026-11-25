# The first reduction step of the reduced fibre theorem

Module `StacksFrontier.AlgebraicGeometry.MoreMorphisms.ReducedFibreReduction`, an extract of the file of the same path of the Lean library AxiomMath/Stacks. The origin of the file and what the extract leaves out are given at the end of this page.

Let `A` be a Dedekind Nagata domain with fraction field `K` and `f : X ⟶ Spec A` flat, quasi-compact and locally of finite type. The reduced fibre theorem (Tag 09IL) begins by making the generic fibre nice: after a finite purely inseparable extension `L/K`, the reduction of `X_L` has a dense open smooth over `L`. The file carries out this step, shows that the integral closure `B` of `A` in `L` is again Dedekind, and proves the finiteness of the bad points used later.

## Main results

- `finite_irreducibleComponents_of_quasiCompact_over_field`, `finite_irreducibleComponents_isCompact_of_locallyOfFiniteType`: for schemes locally of finite type, finitely many irreducible components when quasi-compact over a field, and on quasi-compact opens over a Noetherian ring.
- `ker_eq_nilradical_of_surjective`: a surjective closed immersion with reduced source has kernel the nilradical of the target.
- `exists_finite_purelyInseparable_extension_dense_open_smooth_reduction`: for `X` locally of finite type over a field `k` with finitely many irreducible components, some finite purely inseparable `k'/k` makes the reduction of `X ×_k k'` carry a dense open smooth over `k'`.
- `exists_finite_extension_dense_open_smooth_reduction_genericFibre`: for `A` a domain and `f` quasi-compact and locally of finite type, the same for the base change of `X` to `Spec L`, with `L/K` finite purely inseparable.
- `isDedekindDomain_integralClosure_of_isNagataRing`: for `A` Dedekind and Nagata and `L/K` finite, the integral closure of `A` in `L` is Dedekind; no separability is assumed.
- `isFinite_normalization_pullback_integralClosure`: the normalization of the base change of a scheme locally of finite type along `Spec` of that closure is finite.
- `exists_dense_open_smooth_normalization`: a reduced `Z` locally of finite type over a field with a dense smooth open `U` has normalization with a dense smooth open, the preimage of `U`.
- `finite_setOf_notMem_smoothLocus_mem_genericPoints_fiber`: for `A` Dedekind and `g : Y ⟶ Spec A` flat, quasi-compact, locally of finite type, with a dense smooth open in the generic fibre, only finitely many points lie outside the smooth locus and are generic in their own fibre.

## Proofs

The extension comes from the library's result that a finite purely inseparable extension makes the reduction geometrically reduced, together with the equivalence, for reduced schemes locally of finite type over a field, between geometric reducedness and having a dense smooth open. For the normalization, a smooth scheme is normal, so the normalization is an isomorphism over `U`, and it is birational.

## Watch for

- The reduction is not named as `X.nilradical.subscheme` but by a surjective closed immersion `ρ` with reduced source and nilradical kernel.
- `L/K` is purely inseparable, which is why the Dedekind property of `B` is drawn from the Nagata hypothesis.
- The module docstring lists an open-map result that the file does not contain.

## References

Tags 09IL, 04KT, 056V, 035S.

## References to EGA and SGA

| Source | Place | Declaration | Note |
| --- | --- | --- | --- |
| EGA | II 6.5.1 | `finite_irreducibleComponents_of_quasiCompact_over_field` | special case |
| EGA | II 7.4.1 | `finite_irreducibleComponents_of_quasiCompact_over_field` | partial |
| EGA | IV 4.4.1 | `finite_irreducibleComponents_of_quasiCompact_over_field` | partial |
| EGA | I 7.3.3 | `finite_irreducibleComponents_isCompact_of_locallyOfFiniteType` | special case |
| EGA | II 6.5.1 | `finite_irreducibleComponents_isCompact_of_locallyOfFiniteType` | special case |
| EGA | IV 2.3.6 | `finite_irreducibleComponents_isCompact_of_locallyOfFiniteType` | special case |
| EGA | IV 17.15.13 | `exists_finite_purelyInseparable_extension_dense_open_smooth_reduction` | more general |
| SGA | 4½ Th_finitude 2.7 | `exists_finite_purelyInseparable_extension_dense_open_smooth_reduction` | special case |
| EGA | IV 17.15.13 | `exists_finite_extension_dense_open_smooth_reduction_genericFibre` | more general |
| EGA | IV 9.5.7 | `isDedekindDomain_integralClosure_of_isNagataRing` | B |
| SGA | 5 VI 1.4.7 | `isDedekindDomain_integralClosure_of_isNagataRing` | A is a Dedekind ring |

## Origin of the file

Extracted from the Lean library AxiomMath/Stacks (https://github.com/AxiomMath/Stacks), commit `c496df0d9beea9deaeabcea8492605f9a0a2313b`, file `StacksFrontier/AlgebraicGeometry/MoreMorphisms/ReducedFibreReduction.lean`. That library is distributed under the Apache License, Version 2.0; its licence text is kept with the Library's licences.

Changes made in the extract:

- Of the 11 declarations of the source file 10 are kept. The 1 left out are not needed by the results for which the extract is made: `AlgebraicGeometry.isOpenMap_of_isPullback_integralClosure_of_isNagataRing`.
- The import lines are those that the kept text needs.
- The library's Lean options that differ from Lean's defaults are set at the top of the file (`autoImplicit false`, `maxSynthPendingDepth 3`).
- The import of the library's own attribute modules is replaced by `Mathlib.Tactic.CrossRefAttribute`.
- 11 references to EGA and SGA, written in the source as attributes of that library, are taken out of the Lean text and listed above.
