# Abstract reciprocity: the maps of the three reductions

Module `Nyll.ClassFieldTheory.AbstractClassFieldTheory.Reciprocity.Reduction`, copied unchanged from the Lean library NYLL. The origin of the file is given at the end of this page.

In abstract class field theory over a topological group `G`, fields are closed subgroups and a finite Galois extension L/K is a `FiniteGaloisSubextension K`. A subgroup S of G(L/K) cuts out an intermediate field M (`L.intermediateField S`). This file builds the Galois-side and norm-side arrows among L, M and K used in the reduction steps of the reciprocity theorem, and proves the purely algebraic diagram chases; reciprocity maps themselves enter only as arguments.

## Norm side

- `intermediateNormMap`: the map induced by the norm from M to K between the norm quotients of L/M and L/K (A_M and A_K modulo norms from A_L), defined without assuming M/K normal; `intermediateNormQuotientInclusion` is the map induced by A_K ⊆ A_M.
- `intermediateNormMap_comp_inclusion`: their composite is multiplication by [M : K].

## Galois side

- `lowerInclusionHom` G(L/M) → G(L/K), injective; `upperRestrictionHom` G(L/K) → G(M/K) for normal S, surjective with kernel S (`upperRestrictionHom_eq_one_iff`); `intermediateGalois_exact` says the row is exact. If G(L/K) is cyclic, so are G(L/M) and, for normal S, G(M/K).
- `abelianIntermediateField`, `abelianRestrictionHom`: the field cut out by the commutator subgroup, and restriction to it, with kernel the commutator subgroup.
- `exists_cyclicIntermediateFields`: if G(L/K) is commutative, there are finitely many surjections onto cyclic groups ℤ/mᵢ (mᵢ > 1) with trivial joint kernel, whose fixed fields are finite cyclic over K.
- `inertiaImage`, `maximalUnramifiedSubextension`: the image of the inertia of K in G(L/K) and its fixed field M. M/K is unramified, L/M totally ramified, and M contains every unramified intermediate extension (`maximalUnramifiedSubextension_le_of_isUnramified`).
- `maximalUnramified_normMap_injective`: for cyclic G(L/K), M the maximal unramified subextension, and under `hcf : SatisfiesClassFieldAxiom A`, the norm map from the norm quotient of L/M to that of L/K is injective; it assumes K finite over the base field.

## Diagram chases

- `abstractReciprocity_surjective_of_exact_diagram` and `abstractReciprocity_bijective_of_exact_diagram`: a five-lemma-type argument for two rows of additive groups and three vertical maps.
- `abstractReciprocity_abelianReduction_kernel`: given a commuting square with injective map on the abelian part, the kernel of r is the commutator subgroup; `abstractReciprocity_commutator_mem_kernel` gives one inclusion.
- `abstractReciprocity_cyclicFactors_injective`: injectivity of r from injectivity of the factor maps on a family of quotients with trivial joint kernel (cyclicity is not assumed).

## Points to watch

The surjectivity chase assumes commuting squares, an exact bottom row, a surjective top projection and surjective outer maps; the bijectivity chase adds an exact top row, an injective first bottom map and bijective outer maps; the kernel and cyclic-factor lemmas assume commuting squares and injective outer maps. The file does not prove these for the actual reciprocity maps. The injectivity of the maximal-unramified norm map is taken from `abstractReciprocity_cyclicTower_normMap_injective`, which is not in this file.

## Origin of the file

Copied unchanged from the Lean library NYLL (https://github.com/n-yamaguchi-0729/NYLL), commit `fe40c03df1b2b195053fdd63305571d97c73ce48`, file `Nyll/ClassFieldTheory/AbstractClassFieldTheory/Reciprocity/Reduction.lean`: the Lean file is the source byte for byte (SHA-256 `18fd439ecd5309e48c2a8c98cdf01cd95e5673f1a46ae593a20e32af4a11b0a2`). That library is distributed under the Apache License, Version 2.0; its licence and notice are kept with the Library's licences.
