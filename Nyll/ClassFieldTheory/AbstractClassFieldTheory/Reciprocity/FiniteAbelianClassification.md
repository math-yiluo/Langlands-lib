# Classification of finite abelian extensions by norm subgroups

Module `Nyll.ClassFieldTheory.AbstractClassFieldTheory.Reciprocity.FiniteAbelianClassification`, copied unchanged from the Lean library NYLL. The origin of the file is given at the end of this page.

This file proves the classification theorem of the library's abstract class field theory. Let `G` be a compact, Hausdorff, totally disconnected group, `K` a finite abstract field, and `A`, `D`, `v` a coefficient representation, degree datum and valuation datum. Assume `A` satisfies the class field axiom. Then `L ↦ N(A_L)`, with `N` the norm from `L` to `K`, is an order-reversing bijection between the finite abelian extensions of `K` and the subgroups of `A_K` that are open for the norm topology. It sends composita to intersections and intersections to sums.

## Main results

The results below assume `hcf : SatisfiesClassFieldAxiom A` and the topological hypotheses on `G`; `NormOpenAddSubgroup`, `normSubgroupMap` and the helpers do not.

- `NormOpenAddSubgroup A K`: the additive subgroups of `A_K` open for the norm topology (predicate `IsNormOpen`), ordered by inclusion.
- `normSubgroupMap`: the map `L ↦ N(A_L)` into `NormOpenAddSubgroup`. That norm subgroups are open is taken from `normSubgroup_isOpen`.
- `normSubgroup_compositum`: `N(L₁L₂) = N(L₁) ∩ N(L₂)`.
- `le_iff_normSubgroup_le`: `L₁ ≤ L₂` if and only if `N(L₂) ≤ N(L₁)`.
- `normSubgroupMap_injective`, `normSubgroupMap_surjective` and `normSubgroupMap_bijective`.
- `normSubgroupOrderIso`: the order isomorphism `FiniteAbelianSubextension K ≃o (NormOpenAddSubgroup A K)ᵒᵈ`.
- `normSubgroup_intersection`: `N(L₁ ∩ L₂) = N(L₁) + N(L₂)`.
- `classFieldCandidate_normSubgroup_eq`: let `E` be finite Galois with `N_E ≤ H`. Carry `H / N_E` to the abelianization of `G(E/K)` by the norm residue symbol `D.normResidueSymbol`, take the preimage in `G(E/K)`, and take its fixed field. This candidate has norm subgroup exactly `H`.

Group-theoretic helpers: the restriction maps from the Galois group of a compositum are jointly injective (`compositumRestriction_joint_injective`). Two nested finite abelian extensions with Galois groups of the same order are equal (`eq_of_le_of_extensionQuotient_card_eq`). A sum of norm subgroups is norm-open (`sup_normSubgroup_isOpen`).

## Proof

The unit-cohomology axiom is first derived from `hcf` (`classFieldAxiom_implies_unramifiedUnitCohomology`). Finite reciprocity is then bijective for every finite abelian extension, by a private lemma.

- Compositum: an element of `N(L₁) ∩ N(L₂)` corresponds to some `σ ∈ G(L₁L₂/K)`. By naturality, `σ` restricts trivially to `L₁` and to `L₂`, so `σ = 1`.
- Order reversal: if `N(L₂) ≤ N(L₁)`, then `N(L₁L₂) = N(L₂)`. Reciprocity gives Galois groups of equal order, hence `L₂ = L₁L₂`.
- Surjectivity: every norm-open subgroup contains some `N_E` (`normOpenAddSubgroup_contains_finiteNormSubgroup`), and the candidate field above has the required norm subgroup.

## Watch for

- The class field axiom is a hypothesis throughout. The unit-cohomology axiom is derived here, not assumed.
- "Open" means open for the library's norm topology. It is carried as the predicate `IsNormOpen`, not as a topology instance on `A_K`.
- `FiniteAbelianSubextension` is the library's own structure, and `classFieldCandidate` constructs one; both are defined elsewhere.

## Origin of the file

Copied unchanged from the Lean library NYLL (https://github.com/n-yamaguchi-0729/NYLL), commit `fe40c03df1b2b195053fdd63305571d97c73ce48`, file `Nyll/ClassFieldTheory/AbstractClassFieldTheory/Reciprocity/FiniteAbelianClassification.lean`: the Lean file is the source byte for byte (SHA-256 `b6fc060cd219eb4468cf392a15ae045d7d992e331a6ed59a55ccb4a9e29bae8c`). That library is distributed under the Apache License, Version 2.0; its licence and notice are kept with the Library's licences.
