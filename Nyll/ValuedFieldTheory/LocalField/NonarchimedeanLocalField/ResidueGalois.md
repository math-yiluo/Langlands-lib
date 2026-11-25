# The Galois action on the residue field and the inertia subgroup

Module `Nyll.ValuedFieldTheory.LocalField.NonarchimedeanLocalField.ResidueGalois`, copied unchanged from the Lean library NYLL. The origin of the file is given at the end of this page.

Let `L/K` be an extension of fields with valuative relations and compatible valuations, such that `𝒪[L]` is the integral closure of `𝒪[K]` in `L`. Each `σ ∈ Gal(L/K)` then acts on `𝒪[L]` (by a construction from an imported file) and hence on the residue field `𝓀[L]`. This file builds the resulting homomorphism `Gal(L/K) → Aut(𝓀[L]/𝓀[K])`, identifies its kernel with the inertia subgroup of `𝓂[L]`, and, for finite Galois extensions of local fields, computes the order of that kernel as the ramification index.

## Main definitions and results

- `galoisGroupResidueFieldEquivOfIsIntegralClosure`, `galoisGroupResidueAlgEquivOfIsIntegralClosure`: the automorphism of `𝓀[L]` induced by `σ`, which fixes `𝓀[K]`; it is computed on residues of integers and of integral units.
- `galoisGroupResidueAlgEquivHomOfIsIntegralClosure : Gal(L/K) →* (𝓀[L] ≃ₐ[𝓀[K]] 𝓀[L])`, the residue representation. `galoisGroupResidueStabilizerHomFromGaloisGroupOfIsIntegralClosure_eq` says it agrees with Mathlib's stabilizer map `Ideal.Quotient.stabilizerHom` composed with the map into the stabilizer of `𝓂[L]`.
- `galoisGroupMaximalIdealInertiaOfIsIntegralClosure`: the inertia subgroup of `𝓂[L]` in Mathlib's sense, for this action.
- `galoisGroupResidueAlgEquivHomOfIsIntegralClosure_ker_eq_maximalIdealInertia`: the kernel of the residue representation is the inertia subgroup. Equivalently, `σ` is in the kernel exactly when `σ x - x ∈ 𝓂[L]` for every `x ∈ 𝒪[L]`.
- `galoisGroup_sum_residue_eq_residueAlgEquiv_sum_of_isIntegralClosure`: for `L/K` finite-dimensional and `a ∈ 𝒪[L]`, reducing `Σ_σ σ a` gives the sum, over the same `σ ∈ Gal(L/K)`, of the induced residue automorphisms applied to the residue of `a`.
- For finite Galois `L/K` of nonarchimedean local fields: the inertia subgroup and the kernel have order `ramificationIdxIn` of `𝓂[K]` in `𝒪[L]`, equal to the ramification index of `𝓂[L]` over `𝒪[K]`; if that index is `1`, the kernel is trivial (`..._ker_card_eq_one_of_ramificationIdx_eq_one`).

## Proofs

The kernel statement is Mathlib's `Ideal.Quotient.ker_stabilizerHom`; the order of inertia is Mathlib's `Ideal.card_inertia_eq_ramificationIdxIn`, fed with module-finiteness from integral closure and separability of the finite residue extension from the companion file on residue extensions.

## Points to watch

- `IsIntegralClosure 𝒪[L] 𝒪[K] L` is a hypothesis throughout, and the action on `𝒪[L]` comes from an imported file.
- Surjectivity of the residue representation is not stated here.
- The ramification index used here is `Ideal.ramificationIdx` (or `ramificationIdxIn`), while the degree formula of the residue-extension file uses `Ideal.ramificationIdx'`; relating the two is not part of this file.

## Origin of the file

Copied unchanged from the Lean library NYLL (https://github.com/n-yamaguchi-0729/NYLL), commit `fe40c03df1b2b195053fdd63305571d97c73ce48`, file `Nyll/ValuedFieldTheory/LocalField/NonarchimedeanLocalField/ResidueGalois.lean`: the Lean file is the source byte for byte (SHA-256 `37597c836112bc6d2f18779e8893a6f92292d6d430e616b040ad482139c32332`). That library is distributed under the Apache License, Version 2.0; its licence and notice are kept with the Library's licences.
