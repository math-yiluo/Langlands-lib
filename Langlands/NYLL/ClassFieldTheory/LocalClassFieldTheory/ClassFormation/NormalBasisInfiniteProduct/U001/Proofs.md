# Integral representative of a base-uniformizer lattice element

Worker 519 proves the exact published target
`Langlands.NYLL.LocalClassFieldTheory.chosenBaseUniformizerPow_integerRingFieldSubmodule_exists_mem_maximalIdeal_powStatement`
with the source-adapted theorem of the same name without `Statement`.
All universes, instances, binder kinds and hypotheses are retained.

Unfolding the image-submodule membership provides `x = π_K^m y` with integral
`y`. Regard `y` as an element of `𝒪[L]`. The published
`chosenIntegerRingUniformizer_maximalIdeal_eq` shows that the chosen base
uniformizer is in the base maximal ideal. Mathlib's
`Valuation.HasExtension.algebraMap_mem_maximalIdeal_iff` places its image `πL`
in the extension maximal ideal. The witness `πL^m * y` lies in its `m`-th
power by `Ideal.pow_mem_pow` and `Ideal.mul_mem_right`; coercion to the field
and `map_pow` establish the required equality.

This adapts M150.001, lines 40–59 of
`Nyll/ClassFieldTheory/LocalClassFieldTheory/ClassFormation/NormalBasisInfiniteProduct.lean`
at Naganori Yamaguchi's `n-yamaguchi-0729/ClassFieldTheory` commit
`fbd320cd8b1b06487c58227e92eb135794267709`. The definitional membership steps
replace the source's M144.015 and M144.046 theorem calls, and the inlined
maximal-ideal argument is M144.042, lines 687–695 of
`Nyll/GaloisCohomology/Cyclic/Herbrand/NormalBasisLattice.lean` at that commit.
No duplicate public theorem for those prerequisites is introduced.

The pinned source is readable under
`/home/taskhub/pilot/literature/External Lean project reuse survey- pinned source snapshots, 21 October 2026/n-yamaguchi-0729--ClassFieldTheory/source/`.
Registrations: `external-lean-reuse-snapshots-2026-10-21`, fingerprint
`26e8c647ade044fe9bd4dd1f9d997d4ca12aaa4766e55ab31cb64ca9f8415e01`, and
`nyll-classfieldtheory-fbd320cd-supplement`, fingerprint
`a81005c3aceabc51e9193cdc643d4dd81dd9d496dca2a0cf0111ce610d5b0330`.
No applicable NYLL erratum was found in the Library.

Modifications: focused imports and module, namespace prefix, explicit exact-target
telescope, and the inlined prerequisite arguments above. Original copyright
and author header retained; `licenses/NYLL/LICENSE` and `licenses/NYLL/NOTICE`
apply. This support lemma makes no host class-formation or reciprocity claim.
