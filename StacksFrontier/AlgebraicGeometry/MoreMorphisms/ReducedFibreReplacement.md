# Replacing the base by an integral closure and the scheme by its normalized base change

Module `StacksFrontier.AlgebraicGeometry.MoreMorphisms.ReducedFibreReplacement`, an extract of the file of the same path of the Lean library AxiomMath/Stacks. The origin of the file and what the extract leaves out are given at the end of this page.

Let `A` be a Nagata Dedekind domain with fraction field `K` and `f : X ⟶ Spec A` flat, quasi-compact and locally of finite type. The proof of the reduced fibre theorem (Tag 09IL) first replaces `A` by its integral closure `B₀` in a finite extension `L₀/K`, and `X` by the normalization `Y₀` of the base change of `X` to `Spec B₀`, so that the generic fibre of `Y₀ ⟶ Spec B₀` has a dense smooth open. The file carries out that replacement and checks that the new scheme is normal and again flat, quasi-compact and locally of finite type over the new base.

## Main results

- `flat_locallyOfFiniteType_quasiCompact_normalization_pullback`: for `L/K` finite and `B` the integral closure of `A` in `L`, the normalization `Y` of the base change of `X` to `Spec B` is normal, and `Y ⟶ Spec B` is flat, locally of finite type and quasi-compact.
- `exists_reduction_dense_open_smooth_pullbackLeftPullbackSndIso`: a surjective closed immersion with reduced source presenting the reduction of `X ×_S R`, with a dense open smooth over `R`, gives one for `(X ×_S T) ×_T R` with nilradical kernel.
- `exists_finite_extension_dense_open_smooth_genericFibre_normalization`: there is a finite `L₀/K` such that the fibre of `Y₀ ⟶ Spec B₀` over the generic point has a dense open smooth over the residue field there.

## Proofs

Flatness of `Y ⟶ Spec B` uses that `B` is Dedekind; the finiteness properties hold because the normalization morphism is finite over a Nagata base. The final theorem takes the purely inseparable extension of the first paragraph of the proof, which gives a dense smooth open on the reduction of the direct base change of `X` to `Spec L₀`, rewrites that scheme as the base change to `Spec L₀` of the base change of `X` to `Spec B₀`, and uses that normalization commutes with base change to the fraction field.

## Watch for

- The existential statement does not record that `L₀/K` is purely inseparable, nor the properties of `B₀`. That `B₀` is Dedekind is rederived from the Nagata hypothesis `hA` through `isDedekindDomain_integralClosure_of_isNagataRing`, from another file, not through separability.
- The module docstring, and the docstring of the last theorem, cite a result on the closure (Nagata, Dedekind, with fraction field `L`) that the file does not contain.

## References

Tags 09IL, 032T, 035N.

## Origin of the file

Extracted from the Lean library AxiomMath/Stacks (https://github.com/AxiomMath/Stacks), commit `c496df0d9beea9deaeabcea8492605f9a0a2313b`, file `StacksFrontier/AlgebraicGeometry/MoreMorphisms/ReducedFibreReplacement.lean`. That library is distributed under the Apache License, Version 2.0; its licence text is kept with the Library's licences.

Changes made in the extract:

- Of the 4 declarations of the source file 3 are kept. The 1 left out are not needed by the results for which the extract is made: `AlgebraicGeometry.isDedekindDomain_isNagataRing_isFractionRing_integralClosure`.
- The import lines are those that the kept text needs.
- The library's Lean options that differ from Lean's defaults are set at the top of the file (`autoImplicit false`, `maxSynthPendingDepth 3`).
- The import of the library's own attribute modules is replaced by `Mathlib.Tactic.CrossRefAttribute`.
- The 2 references to EGA and SGA that the source writes as attributes of that library belong to the declaration left out; none remains.
