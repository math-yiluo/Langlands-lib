# Permutation bases over a prescribed splitting field

Worker 1550. This internal deduction transports the basis in the published
`IsInducedTorus` predicate to any prescribed finite Galois splitting field.
It uses the actual character lattices and their published Galois
representations. All fields and basis indices remain in an arbitrary universe
`u`; the argument includes every characteristic and an empty basis index.

`characterLattice.fieldTestMap e` is the morphism of tests over `Spec k`
associated to a field embedding `e : E →ₐ[k] M`. The map on schemes is
`Spec e`, and its compatibility with the base follows from the algebra
homomorphism law. `characterLattice.restriction_galois` says that character
restriction along this map commutes with automorphisms `σ` of `E` and `τ` of
`M` when `τ(e x) = e(σ x)` for every `x`. The proof rewrites both actions as
character restriction, uses the restriction composition law, and applies the
contravariance of `Spec` to the compatibility equation. No splitting or
finiteness hypothesis is needed for this compatibility theorem.

`characterLattice.field_restriction_bijective` specializes the split-character
restriction theorem: if `T_E` is split, restriction from its character lattice
to that of `T_M` is bijective for any field embedding `E →ₐ[k] M`.
`IsSplitTorus.finite_character_basis` proves that any integral character basis
of a split torus over a field has finite index. A chosen split presentation
identifies its lattice with `J → ℤ` for a finite type `J`; the resulting finite
module structure forces any basis index to be finite.

The main theorem `IsInducedTorus.exists_permuted_basis` assumes an induced
commutative group scheme `T` over `k` and a finite Galois extension `L/k` over
which `T` is split. It produces a type `I : Type u`, a proof of `Finite I`,
and a basis of `X*(T_L)` indexed by `I`, such that for every `σ : L ≃ₐ[k] L`
and `i : I` the actual Galois action on the `i`th basis vector equals some
`j`th basis vector.

The implemented proof chooses a witness `E/k` and permuted basis from
`IsInducedTorus T`. It embeds `E` and `L` into `Ω = AlgebraicClosure k` by
`IsAlgClosed.lift` and installs the algebra structures induced by those
embeddings. Restriction from each split lattice to `X*(T_Ω)` is bijective.
Composing the first additive equivalence with the inverse of the second
transports the original basis to `L`. The original split presentation proves
its index finite. For an automorphism `σ` of `L/k`, `AlgEquiv.liftNormal`
extends it to `τ` of `Ω/k`, and normality of `E/k` gives the restriction `ρ`
to `E`. Compatibility of restriction with Galois actions transfers the basis
permutation by `ρ` to the required permutation by `σ`. Injectivity of the
restriction from `L` establishes the final equality.

Provenance is internal: the constructions and proofs combine
`Torus.CharacterRestriction`, `Torus.LatticeGalois`, `Torus.Lattice`, and the
published `IsInducedTorus` predicate with Mathlib's algebraic-closure and
normal-extension APIs. The unit supplies the prescribed-field basis step;
it does not assert a Weil decomposition or prove the final decomposition
statement.
