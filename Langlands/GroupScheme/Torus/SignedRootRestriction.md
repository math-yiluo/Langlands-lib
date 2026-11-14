# Signed root sets under restriction to a split subtorus

Module `Langlands.GroupScheme.Torus.SignedRootRestriction`.

## Content

Let `k` be a field, `T` and `A` split tori over `k` (commutative group
schemes with `IsSplitTorus`), and `H`, `Q` group schemes over `k` that are
affine and locally of finite type. Let `ρ : T ⟶ A` be a homomorphism, and let
`b : A ⟶ H` and `a : A ⟶ Q` be homomorphisms of group schemes. Let
`sT : X^*(T) → ℝ` and `sA : X^*(A) → ℝ` be functions on the character
lattices. They are compatible with `ρ`: `sT (ψ ∘ ρ) = sA ψ` for every
character `ψ` of `A`.

`roots_comp_eq_nonneg_of_roots_eq_nonneg` says the following. Suppose the
roots of `A` acting on `Lie(H)` through `b` are exactly the roots of `A`
acting on `Lie(Q)` through `a` with `sA ≥ 0`. Then the roots of `T` acting
on `Lie(H)` through `ρ ≫ b` are exactly the roots of `T` acting on
`Lie(Q)` through `ρ ≫ a` with `sT ≥ 0`.

Here `roots i` is the Library's set of nonzero characters with a nonzero
weight space on the Lie algebra of the target (`Torus/Weights.lean`). The
typical use takes `sA ψ = ⟨ψ, v'⟩` and `sT χ = ⟨χ, v⟩` for points `v`, `v'`
of the real cocharacter spaces with `ρ_*(v) = v'`.

## Proof

Both sides are rewritten with the Library lemma `mem_roots_comp_iff`
(`Torus/WeightRestriction.lean`). For split `T` and `A`, a character `χ` of
`T` is a root through `ρ ≫ i` if and only if `χ ≠ 0` and `χ = ψ ∘ ρ` for
some root `ψ` of `A` through `i`. Apply this to `i = b` and `i = a`. Given
such a `ψ`, the hypothesis says that `ψ` is a root through `b` exactly when
it is a root through `a` with `sA ψ ≥ 0`. By compatibility,
`sA ψ = sT χ`. The two directions are then direct rewriting.

## Provenance

Internal infrastructure for the proof of
`Langlands.BruhatTits.IntegralModels.UnramifiedFacetCommonTorusStatement`
(Kaletha–Prasad, *Bruhat–Tits theory: a new approach*, Axiom 4.1.22(3)).
In that proof the Lie-weight sign formula is known for a split torus `A`
of the descended model over the maximal unramified extension, and it is
needed for the smaller torus `T` that maps into `A`. The lemma is the
elementary step that roots of a subtorus are the nonzero restrictions of
roots, applied to a sign condition. It makes no further assertion from the
literature.
