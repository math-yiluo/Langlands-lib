# Coefficients of homomorphisms from lattice tori, and central homomorphisms

Author: Worker 1178.

This internal module proves the key coefficient identity behind images of
homomorphisms from lattice tori, and reformulates centrality of natural
homomorphisms by a single universal identity.

## The coefficient identity

`coeffAt m` is the coefficient of `[m]` as a linear functional on `R[Λ]`, and
`sliceAt m` is the linear map `x ⊗ y ↦ coeff_m(y) • x` on `R[Λ] ⊗ R[Λ]`.
`sliceAt_comul`: since the comultiplication is `[n] ↦ [n] ⊗ [n]`,
`sliceAt m (Δ x) = coeff_m(x) • [m]` for every `x`.

`coeff_smul_single_eq`: let `α : latticeFunctor R Λ ⟶ F'` be classified by
`ψ : B' → R[Λ]`, where `F'` is corepresented by `B'` with comultiplication
`Δ'`. Applying `sliceAt m` to the compatibility
`Δ(ψ h) = (ψ ⊗ ψ)(Δ' h)` (from `classify_comul`) gives

`coeff_m(ψ h) • [m] = ψ ( rid ((coeff_m ∘ ψ).lTensor (Δ' h)) )`.

So `coeff_m(ψ h) • [m]` lies in the range of `ψ`, and if
`Δ' h = ∑ aᵢ ⊗ bᵢ` it lies in the span of the `ψ aᵢ`.

## Central natural homomorphisms

`IsCentralNat α` says that every value `α.app S x` commutes with every point
of `F'(S)`. `CentralIdentity d ψ` is the identity
`comul d ≫ pair (ψ ≫ jl) jr = comul d ≫ pair jr (ψ ≫ jl)` of algebra maps
`B' → B ⊗ B'`, where `jl`, `jr` are the inclusions into the tensor product.
`isCentralNat_iff` proves `IsCentralNat α ↔ CentralIdentity d (classify e d α)`:
the forward direction evaluates on the universal points over `B ⊗ B'`; the
converse specializes the identity along `lift2 (cls e x) (cls d y)`.

The module also provides the tensor-product helpers `tens`, `jl`, `jr`,
`lift2`, `pair_comp` and `cancel_injective` (cancellation of an algebra map
with injective underlying function).

## Provenance

Internal. The coefficient identity is the standard argument that a
subcoalgebra of a group algebra is spanned by the group-like elements it
contains, implemented with an explicit slice functional.
