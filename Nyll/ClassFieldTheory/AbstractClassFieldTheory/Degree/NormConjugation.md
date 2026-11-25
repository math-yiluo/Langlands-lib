# Conjugation of abstract fields and relative norms

Module `Nyll.ClassFieldTheory.AbstractClassFieldTheory.Degree.NormConjugation`, copied unchanged from the Lean library NYLL. The origin of the file is given at the end of this page.

Abstract fields are closed subgroups of a group `G` with a topology, and `s ∈ G` sends a field `K` to its right conjugate `K^s`, represented by `s⁻¹ G_K s`. The file shows that conjugation is compatible with field inclusions, coset spaces, normality, finiteness and the relative norm: `N(L^s/K^s)(a^s) = N(L/K)(a)^s`. These identities are prepared for the abstract reciprocity construction and its compatibility with conjugation.

## Main definitions and results

- `conjugateClosedSubgroup_mono`: `G_L ≤ G_K` implies `s⁻¹ G_L s ≤ s⁻¹ G_K s`.
- `conjugateSubgroupEquiv`: the group isomorphism `G_K ≃ s⁻¹ G_K s`, `k ↦ s⁻¹ k s`.
- `map_extensionSubgroup_conjugate`: it carries `G_L` (inside `G_K`) onto `s⁻¹ G_L s` (inside `s⁻¹ G_K s`).
- `relativeConjugateCosetEquiv`: the induced bijection of coset spaces `G_K / G_L ≃ (s⁻¹ G_K s) / (s⁻¹ G_L s)`, with no normality needed.
- `conjugateExtension_normal` (a conjugate of a Galois extension is Galois) and `finite_conjugateExtension` (conjugation preserves finiteness of the coset space).
- `finiteReciprocityNaturalityConjugation`: for normal `G_L`, the group isomorphism `G(L|K) ≃ G(L^s|K^s)`, `τ ↦ s⁻¹ τ s`.
- `relativeNorm_conjugate_apply`: for a `ℤ`-representation `A` of `G`, `G_L` of finite index in `G_K` and `a` fixed by `G_L`, the norm of the conjugated element `s⁻¹ a` is `s⁻¹` applied to the norm of `a`.

The norm identity is proved by reindexing the coset sum along `relativeConjugateCosetEquiv`, using that conjugation intertwines the coset actions term by term.

## Points to watch

- All statements assume `ContinuousMul G`, which is needed only for the conjugate of a closed subgroup to be closed.
- Conjugation is on the right: `K^s` corresponds to `s⁻¹ G_K s`, and `a^s` means `s⁻¹ a`.

## Origin of the file

Copied unchanged from the Lean library NYLL (https://github.com/n-yamaguchi-0729/NYLL), commit `fe40c03df1b2b195053fdd63305571d97c73ce48`, file `Nyll/ClassFieldTheory/AbstractClassFieldTheory/Degree/NormConjugation.lean`: the Lean file is the source byte for byte (SHA-256 `72bcd67bd71a6ba4b762ee17dd48bc3f6b2d8565a2072bf484835e03ea3550a3`). That library is distributed under the Apache License, Version 2.0; its licence and notice are kept with the Library's licences.
