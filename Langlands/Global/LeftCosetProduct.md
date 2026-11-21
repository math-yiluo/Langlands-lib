# Left quotients with an unquotiented direct factor

`Langlands.Global.LeftCosetSpace.productHomeomorph` uses a supplied
isomorphism of topological groups `E : A × N ≃ₜ* G` under which a subgroup
`Γ ≤ G` pulls back to `{1} × H` for `H ≤ N`. It identifies the actual left
quotient `Γ \ G` with `A × (H \ N)` by `[E(a,n)] ↦ (a,[n])`. The quotient
relations agree: `E(b,m) E(a,n)⁻¹ ∈ Γ` means `b = a` and `m n⁻¹ ∈ H`.
The inverse uses any representative of the second component. It is
continuous because `id_A × mk_H` is an open quotient map and the inverse
composed with this map is `mk_Γ ∘ E`. The forward map is measurable for
the inherited quotient sigma algebras whenever `E.symm` is measurable for
the product sigma algebra.

This is an internal product-quotient construction, not a new adelic
structure theorem. Its adelic use is the split-centre convention of Getz
and Hahn, *An Introduction to Automorphic Representations*, §2.6,
(2.19)–(2.22): retaining the positive central coordinate on the principal
quotient and quotienting it out on `[G]`. Unlike the full-factor quotient
`(A × H) \ (A × N)`, this construction does **not** divide out `A`. No
normality, discreteness or measure normalization is part of the homeomorphism.
