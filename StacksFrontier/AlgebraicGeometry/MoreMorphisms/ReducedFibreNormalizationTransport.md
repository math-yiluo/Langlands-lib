# Normalization under isomorphisms and surjective closed immersions

Module `StacksFrontier.AlgebraicGeometry.MoreMorphisms.ReducedFibreNormalizationTransport`, an extract of the file of the same path of the Lean library AxiomMath/Stacks. The origin of the file and what the extract leaves out are given at the end of this page.

The normalization of a scheme has a universal property among morphisms from normal schemes that send generic points to generic points. From it the file draws two invariance statements, each existential: a comparison isomorphism of normalizations exists and commutes with the normalization morphisms. All schemes are assumed to have finitely many irreducible components on quasi-compact opens, as the normalization requires.

## Main results

- `Scheme.exists_normalizationScheme_iso_of_iso`: an isomorphism `e : X ≅ Y` induces `d` between the normalizations with `d ≫ ν_Y = ν_X ≫ e`.
- `Scheme.exists_normalizationScheme_iso_of_ker_eq_nilradical`: a closed immersion `ι : Z ⟶ W` whose kernel is the nilradical of `W` induces `d` from the normalization of `W` to that of `Z` with `d ≫ ν_Z ≫ ι = ν_W`.
- `Scheme.exists_normalizationScheme_iso_of_surjective`: the same for any surjective closed immersion, with neither scheme assumed reduced.

## Proofs

For an isomorphism, each direction is the unique lift through the other normalization, and the composites are identities by uniqueness. A closed immersion with nilradical kernel is identified with the reduction, whose normalization is that of `W` (Tag 035O). The surjective case compares both normalizations with that of `Z_red`, using that the reduction `Z_red ⟶ Z` and the composite `Z_red ⟶ Z ⟶ W` both have nilradical kernel.

## Watch for

The third statement lets the normalization of the base change of `X` along `Spec B ⟶ Spec A` be computed after discarding nilpotents, as the reduced fibre theorem (Tag 09IL) needs, since the comparison of iterated normalized base changes elsewhere asks the scheme being normalized to be reduced.

## References

Tags 035O, 035Q, 09IL.

## Origin of the file

Extracted from the Lean library AxiomMath/Stacks (https://github.com/AxiomMath/Stacks), commit `c496df0d9beea9deaeabcea8492605f9a0a2313b`, file `StacksFrontier/AlgebraicGeometry/MoreMorphisms/ReducedFibreNormalizationTransport.lean`. That library is distributed under the Apache License, Version 2.0; its licence text is kept with the Library's licences.

Changes made in the extract:

- Every declaration of the source file is kept.
- The import lines are those that the kept text needs.
- The library's Lean options that differ from Lean's defaults are set at the top of the file (`autoImplicit false`, `maxSynthPendingDepth 3`).
