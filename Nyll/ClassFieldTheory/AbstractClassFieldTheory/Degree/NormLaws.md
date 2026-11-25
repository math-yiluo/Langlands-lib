# Laws of the relative norm

Module `Nyll.ClassFieldTheory.AbstractClassFieldTheory.Degree.NormLaws`, copied unchanged from the Lean library NYLL. The origin of the file is given at the end of this page.

The file proves the structural laws of the coset-sum norm `N(L/K) : A_L → A_K` attached to closed subgroups `G_L ≤ G_K` of finite index, for a `ℤ`-representation `A` of the group `G`: compatibility of the absolute norm with conjugation, invariance under the action of `G_K` when `L | K` is Galois, and transitivity in towers. It also introduces conjugate abstract fields.

## Main definitions and results

- `conjugateClosedSubgroup K σ`: the closed subgroup `σ⁻¹ G_K σ`, representing the right conjugate field `K^σ` (membership: `σ x σ⁻¹ ∈ G_K`, `conjugateClosedSubgroup_mem`).
- `conjugateFixedElement`: for `a` fixed by `G_K`, the element `a^σ = σ⁻¹ a`, fixed by `σ⁻¹ G_K σ`.
- `absoluteConjugateCosetEquiv`: conjugation identifies the coset spaces `G / (σ⁻¹ G_K σ)` and `G / G_K`.
- `relativeNorm_absoluteConjugate_apply`: if `G_K` has finite index in `G`, the norm from `K^σ` to the base field of `σ⁻¹ a` equals `σ⁻¹` applied to the norm of `a` from `K`.
- `normalExtensionAction`: when `G_L` is normal in `G_K`, an element of `G_K` acts on `A_L`; `relativeNorm_normalExtensionAction`: the norm is invariant under this action.
- `relativeTowerQuotientFinite`: finite index is transitive in towers `G_M ≤ G_L ≤ G_K`. `DegreeData.FiniteTower.totalExtension` is the composite finite extension of a finite tower.
- `DegreeData.FiniteTower.norm_trans_apply` and `norm_trans`: `N(L/K) ∘ N(M/L) = N(M/K)` along a finite tower.

## Proofs

Each law is a reindexing of the finite coset sum: through the conjugation bijection, through right multiplication by `k` on `G_K / G_L`, and through the bijection `G_K / G_M ≃ G_K / G_L × G_L / G_M` from the imported quotient-tower file, which uses chosen coset representatives.

## Points to watch

- Conjugation acts on the right: `K^σ` is `σ⁻¹ G_K σ` and `a^σ` is `ρ(σ⁻¹) a`. `ContinuousMul G` is assumed so that the conjugate subgroup is closed.
- The conjugation law is proved here only for the norm to the base field (the whole group `G`), not for an arbitrary relative norm.
- `normalExtensionAction` takes normality as an explicit hypothesis rather than an instance.

## Origin of the file

Copied unchanged from the Lean library NYLL (https://github.com/n-yamaguchi-0729/NYLL), commit `fe40c03df1b2b195053fdd63305571d97c73ce48`, file `Nyll/ClassFieldTheory/AbstractClassFieldTheory/Degree/NormLaws.lean`: the Lean file is the source byte for byte (SHA-256 `f6401494513fa0e9d6e1f52e525b46abd014e65fba2558df0581d80b264a1a22`). That library is distributed under the Apache License, Version 2.0; its licence and notice are kept with the Library's licences.
