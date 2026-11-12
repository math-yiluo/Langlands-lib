# Continuity of the Galois action on the lattices of a torus: statement

Author: Worker 15, for the algebraic and reductive group-scheme program
`2b5e4a00-9d44-49a4-9c89-979fb5b6233e` (Task 3483). The module contains one
`Prop`-valued definition and no proof.

## The statement

`Langlands.GroupScheme.TorusLatticeGaloisContinuityStatement` says the following. Let
`k` and `E` be fields in one universe `u`, with an algebra `k → E` that is algebraic
(`Algebra.IsAlgebraic k E`). Let `T` be a commutative group scheme over `Spec k`.
Suppose the base change `T_E` along `algebraBaseMap k E` is a split torus
(`IsSplitTorus`). Then there is an intermediate field `L` of `E/k`, finite-dimensional
over `k`, with this property: every `σ : E ≃ₐ[k] E` fixing `L` pointwise acts as the
identity both on the character lattice `X^*(T_E)` and on the cocharacter lattice
`X_*(T_E)`.

The actions are the Library's `characterLattice.galoisRepresentation k E T` and
`cocharacterLattice.galoisRepresentation k E T` of `Torus/LatticeGalois`. On points,
`σ` sends a character `χ` to `t ↦ σ(χ(σ⁻¹ t))`, and similarly for cocharacters. The
conclusion `galoisRepresentation σ = 1` is equality with the identity endomorphism of
the lattice.

No finiteness, normality or separability of `E/k` is assumed beyond algebraicity. `T`
is not assumed to be of finite type, affine or a torus over `k`. These properties
descend from `T_E`, and that descent is a proof obligation. When `E/k` is Galois, the
subgroups of `E ≃ₐ[k] E` fixing finite-dimensional intermediate fields form a basis of
neighbourhoods of the identity for the Krull topology. The statement then says that
both actions are continuous for the Krull topology and the discrete topology on the
lattices, and in fact factor through a finite quotient.

## Source and provenance

Milne, *Algebraic Groups* (2022 corrected reprint), source `milne-2022-algebraic-groups`,
SHA-256 `f2ddd8fa4d263085f173934664b246007a2c0bd539739b7c82de39bfb5d21f40`, §12.g,
printed p.239 (PDF p.250). Milne lets `Γ = Gal(k_s/k)` act on `X^*(G) = X(G_{k_s})`. He
calls an action on a commutative group `M` continuous "if every element of `M` is
fixed by an open subgroup of `Γ`", that is, `M = ⋃_K M^{Gal(k_s/K)}` over finite
extensions `K`. He states that "because every homomorphism `G_{k_s} → G_{m, k_s}` is
defined over a finite extension of `k`, the action is continuous".

The statement is derived from this. It is stated for an arbitrary algebraic extension
`E` instead of `k_s`, with the full group `E ≃ₐ[k] E`. It includes the cocharacter
lattice, which Milne does not mention here. Because `X^*(T_E) ≅ ℤ^I` is finitely
generated, Milne's elementwise continuity gives one finite `L` for the whole lattice.
The same holds for `X_*(T_E)`. This uniform form is the one used for the star action
on based root data. The ledger of Task 3483 records the absence of a general
continuity theorem for Galois actions on torus lattices. This statement is that
missing result.
