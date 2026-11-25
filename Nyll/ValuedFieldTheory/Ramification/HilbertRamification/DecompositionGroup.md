# Decomposition groups of absolute values and their behaviour in towers

Module `Nyll.ValuedFieldTheory.Ramification.HilbertRamification.DecompositionGroup`, copied unchanged from the Lean library NYLL. The origin of the file is given at the end of this page.

The file defines the decomposition group of a real absolute value `w` on `L` over a subfield `K`, valid for archimedean and non-archimedean `w`, and proves the restriction law for a tower `K ⊆ M ⊆ L`: inside `Aut(L/K)`, the decomposition, inertia and ramification groups over `M` are those over `K` intersected with `Aut(L/M)`. The inertia and ramification statements use valuation subrings and so concern the non-archimedean case.

## Main definitions and results

- `absoluteValueDecompositionGroup K w`: the `K`-automorphisms `σ` with `w(σx) < 1 ↔ w(x) < 1` for every `x : L`.
- `mem_absoluteValueDecompositionGroup_iff_equivalent`: membership means `w ∘ σ` is equivalent to `w`.
- `mem_absoluteValueDecompositionGroup_iff_extensionConjugate_eq`: when `w` is an extension of a nontrivial absolute value `v` of `K`, membership means the conjugate extension `w ∘ σ` equals `w`.
- `decompositionGroupRestriction_restrictAutomorphismScalars_injective`: the inclusion `Aut(L/M) → Aut(L/K)` is injective.
- `decompositionGroupRestriction_absoluteValueDecompositionGroup_range_eq_inf`: the image of the decomposition group over `M` is `D_w(L/K) ∩ Aut(L/M)`.
- `ValuationSubring.decompositionGroupRestriction_inertiaGroupInAut_range_eq_inf` and `ValuationSubring.decompositionGroupRestriction_ramificationGroupInAut_range_eq_inf`: for a valuation subring `A` of `L`, `I(L/M) = I(L/K) ∩ Aut(L/M)` and `R(L/M) = R(L/K) ∩ Aut(L/M)`, for the inertia and ramification groups viewed inside the automorphism group.

## Proofs

The absolute-value statement holds because membership does not depend on the base field. The inertia and ramification statements rest on the restriction-of-scalars membership lemmas for decomposition, inertia and ramification groups from the valuation-subring file.

## Points to watch

- The decomposition group is the stabilizer of the equivalence class of `w` (its open unit ball), not of the chosen representative; the file proves that the two agree for exact extensions of a nontrivial absolute value of `K`.
- No finiteness, Galois or algebraicity hypothesis is made on `L/K` or `L/M`.

## Origin of the file

Copied unchanged from the Lean library NYLL (https://github.com/n-yamaguchi-0729/NYLL), commit `fe40c03df1b2b195053fdd63305571d97c73ce48`, file `Nyll/ValuedFieldTheory/Ramification/HilbertRamification/DecompositionGroup.lean`: the Lean file is the source byte for byte (SHA-256 `35ec8a5deb58fb09c46a6ab4dbeb20017b010c43eeeed763317f9fc85cce94c5`). That library is distributed under the Apache License, Version 2.0; its licence and notice are kept with the Library's licences.
