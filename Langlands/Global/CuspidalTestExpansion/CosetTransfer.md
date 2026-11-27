# Transfer of coset sums along a homomorphism

Module `Langlands.Global.CuspidalTestExpansion.CosetTransfer`
(namespace `Langlands.Global.CosetTransfer`). Pure group theory.

Let `φ : Γ →* H` be a homomorphism of groups, `Λ ≤ Γ` and `A, B ≤ H` subgroups such that
`φ(Γ) ⊆ B`, `φ⁻¹(A) = Λ` (hypothesis `hpre : φ x ∈ A ↔ x ∈ Λ`), and every `b ∈ B` is `a · φ(x)`
with `a ∈ A`.

## Declarations

- `cosetEquiv`: the induced bijection of right coset spaces `Λ \ Γ ≃ (A ∩ B) \ B`
  (`Quotient (rightRel Λ) ≃ Quotient (rightRel (A.subgroupOf B))`), `[x] ↦ [φ x]`.
- `cosetEquiv_out`: the chosen representative of the image of `c` is `a · φ(out c)` for some
  `a ∈ A`.
- `tsum_cosetEquiv`: for `f : H → E` left invariant under `A` and every `y`,
  `∑' c : Λ \ Γ, f(φ(out c) · y) = ∑' c : (A ∩ B) \ B, f(out c · y)`.

## Proofs

`cosetEquiv` is well defined and injective because `φ y φ(x)⁻¹ = φ(y x⁻¹) ∈ A ↔ y x⁻¹ ∈ Λ`, and
surjective by the factorization hypothesis. `tsum_cosetEquiv` reindexes the right-hand sum along
`cosetEquiv` (`Equiv.tsum_eq`) and removes the factor `a ∈ A` from `cosetEquiv_out` by the left
invariance of `f`.
