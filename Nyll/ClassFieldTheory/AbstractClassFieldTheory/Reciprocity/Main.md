# The abstract reciprocity theorem and naturality of the norm-residue symbol

Module `Nyll.ClassFieldTheory.AbstractClassFieldTheory.Reciprocity.Main`, copied unchanged from the Lean library NYLL. The origin of the file is given at the end of this page.

This file completes the reciprocity theorem of abstract class field theory. Here `G` is a compact, Hausdorff, totally disconnected topological group, "fields" are closed subgroups of `G`, `D : DegreeData G` is the degree map, `A : Rep ℤ G` the module and `v : ValuationData D A` a valuation. For a finite Galois extension L/K, where K is a finite abstract field (`K : FiniteAbstractField G`, of finite degree over the base field), it shows that the reciprocity map from G(L/K)ᵃᵇ to A_K modulo the norms from A_L is bijective, defines the norm-residue symbol as its inverse, and proves its three naturality diagrams.

## Main results

The first four results assume `hcf : SatisfiesClassFieldAxiom A` and `hAxiom : v.SatisfiesUnramifiedUnitCohomology D`.

- `abstractReciprocity_cyclic_finiteReciprocityHom_bijective`: for cyclic L/K, `finiteReciprocityHom` is bijective.
- `abstractReciprocity_finiteReciprocityHom_surjective`: for every finite Galois L/K it is surjective.
- `abstractReciprocity_abelian_finiteReciprocityHom_injective`: if G(L/K) is abelian it is injective.
- `abstractReciprocity_abelianizedReciprocity_bijective`: its factor through the abelianization is bijective.
- `DegreeData.abstractReciprocityEquiv`: the isomorphism `Additive (Abelianization G(L/K)) ≃+ FiniteNormQuotient A K L`, under the class field axiom alone. `normResidueSymbol` is its inverse; simp lemmas evaluate the isomorphism on the class of a Galois element q and the symbol on the reciprocity image of q.
- `normResidueNaturality_norm_restriction`, `normResidueNaturality_conjugation`, `normResidueNaturality_transfer_inclusion`: the norm-residue symbol commutes with restriction and the relative norm, with conjugation by `s : G`, and with transfer and inclusion of fixed elements. The pair maps `normResidueNaturality…PairMap` assemble both vertical arrows on G(L/K)ᵃᵇ × A_K/N A_L, with their values on representatives.

## Proofs

In the cyclic case L/K is split at its maximal unramified subextension M: L/M is cyclic totally ramified (from the `TotallyRamifiedCase` files), M/K unramified (`unramifiedReciprocityEquiv`), and a chase in a diagram with exact rows, using injectivity of the norm map from the maximal unramified part, gives bijectivity. Surjectivity is first shown for solvable groups by induction on the order (cutting out a cyclic coordinate, or the commutator subgroup), then in general through a Sylow subgroup. Injectivity for abelian groups uses jointly faithful cyclic quotients. The naturality diagrams come from those of the reciprocity homomorphism by inverting the horizontal isomorphisms.

## Points to watch

- Fields, `FiniteAbstractField`, `FiniteGaloisSubextension`, `FiniteNormQuotient`, `DegreeData` and `ValuationData` are the library's own notions.
- The norm-residue symbol is defined as the inverse of the reciprocity isomorphism, not constructed independently.
- The intermediate theorems carry `hAxiom` separately; `abstractReciprocityEquiv` derives it from the class field axiom by `classFieldAxiom_implies_unramifiedUnitCohomology`.
- The norm quotient is not assumed finite: the Sylow step uses only that every class is killed by the degree.

## Origin of the file

Copied unchanged from the Lean library NYLL (https://github.com/n-yamaguchi-0729/NYLL), commit `fe40c03df1b2b195053fdd63305571d97c73ce48`, file `Nyll/ClassFieldTheory/AbstractClassFieldTheory/Reciprocity/Main.lean`: the Lean file is the source byte for byte (SHA-256 `7ff2c7707ad38827ff5eaa8552e28059417470005407c6ebe11b9cd15ebbbab7`). That library is distributed under the Apache License, Version 2.0; its licence and notice are kept with the Library's licences.
