# Steinberg tensor embeddings of torus-invariant regular functions

`Langlands.GroupScheme.SteinbergTensorEmbeddingStatement` is an unproved
proposition. It is stated so that it can be proved separately. It is the
representation-theoretic input left over in the reduction
`simplyConnectedPositiveCharConjugationMap_of_steinberg`, which derives
`SimplyConnectedPositiveCharConjugationMapStatement` from it.

## Statement

Fix an arbitrary universe `u`. Let `k : Type u` be an algebraically closed field
of prime characteristic `p`, and let `G` be an actual `k`-group scheme that is
simply connected in the Library's algebraic sense, which includes semisimplicity.
The binder `[IsAffine G.X.left]` is needed to form the coordinate algebra
`AffineCoordinates.algebra G`. It adds no hypothesis, because simple
connectedness implies it: semisimple groups are connected reductive, so their
structure morphism is affine. The reduction proves this instance from
`IsSimplyConnected G` before applying the proposition.

The proposition asks for an abelian group `Λ : Type u` and an actual group
scheme homomorphism `j` from the diagonalizable group `D(Λ)` to `G` with the
following property. Let `V` be a subspace of the coordinate algebra with a
finite basis `b` indexed by `Fin d`, and suppose `V` is stable under the right
regular coaction, meaning `rightAct f w ∈ V` for every linear form `f` and every
`w ∈ V`. Suppose also that every `w ∈ V` is left-invariant under `j`: for every
test scheme `T`, every `T`-point `h` of `D(Λ)` and every `T`-point `g` of `G`,
evaluating `w` at `j(h) * g` gives the same value as evaluating it at `g`. Then
there are

- a size `m`,
- actual representations `σ` and `π` of `G` on `k^(Fin m)`, and
- a matrix `C` from `k^(Fin d)` to `k^(Fin m × Fin m)`,

such that the rational representation of `σ` is irreducible, `C` intertwines
the finite regular representation `Chevalley.affineRegularRepresentation G V b hV`
with the actual tensor representation `σ.tensor π` on every test algebra, and `C`
is injective.

Every quantifier is over actual objects: representations, intertwiners and
invariance are tested on all test schemes or test algebras, not only on rational
points. Only irreducibility uses the rational-point representation
`rationalRepresentation`, which is the notion used by the existing
`ConjugationSchur` and `NondegenerateTensorConjugation` adapters.

## Provenance

This is an internal interface. It is extracted from the proof sketch of
Theorem A.1.0, (a) implies (b), in Mumford, Fogarty and Kirwan, *Geometric
Invariant Theory*, third enlarged edition (1994), Appendix to Chapter 1,
Section A, printed p.192. The registered source is
`mumford-fogarty-kirwan-1994-git-3rd`, SHA-256
`25b78ea299e007fbabefb23e9dd7d30beba86c5c1eaa9718b8cc3f98f54932b2`.

In that sketch `T` is a maximal torus contained in a Borel subgroup `B`, `ρ` is
half the sum of the positive roots, and `W_(mρ) = H^0(G/B, L(mρ))`. Steinberg's
results give that `W_(mρ)` is irreducible and self-dual when `m = p^s - 1`. The
sketch then states that, with `T` acting on the right, the `T`-invariant regular
functions on `G` form an increasing union of copies of `W_(mρ) ⊗ W_(mρ)` as `m`
increases, with `G` acting on the left.

The present proposition records only what the reduction uses from this claim.

- **Side convention.** The Library's finite regular representations use right
  translation with left invariance. Inversion on `G` exchanges this with the
  source's left action and right invariance.
- **Torus.** The proposition asks for some diagonalizable `j`, not necessarily
  a maximal torus. This is weaker than the source's choice. The intended witness
  is a split maximal torus `T ≅ D(ℤ^r)`, with `ℤ^r` lifted to universe `u`.
- **Tensor factors.** It does not ask for the two factors to be equal,
  self-dual, of `p`-power dimension, or Steinberg modules, and it does not ask
  for the whole invariant algebra to be exhausted. It asks only for an injective
  equivariant embedding of each finite stable invariant subspace into one
  tensor product whose first factor is irreducible and whose two factors have
  the same size.

The containment `V ⊆ image` for one large `m = p^s - 1` follows from the
increasing-union claim, because `V` is finite-dimensional. Injectivity is the
source's "copies". When `V = 0` the trivial one-dimensional representation
is a witness.

## Expected proof

A proof is expected to follow the source and is not supplied here. Take `T` a
maximal torus with Borel subgroups `B ⊇ T` and `B^-` opposite, and
`λ = (p^s - 1)ρ`. Simple connectedness makes `ρ` a character of `T`.

1. Multiplying sections gives a `G`-map from
   `H^0(G/B, L(λ)) ⊗ H^0(G/B^-, L(-λ))` to the `T`-invariant functions. These
   are the regular functions on the open orbit `G/T` of `G/B × G/B^-`.
2. Because the orbit is dense, restriction of sections is injective.
3. The invariant section `τ_ρ` of `L(ρ) ⊠ L(-ρ)` restricts to `1` and vanishes
   exactly on the complement of the orbit. Since this line bundle is ample,
   every invariant function has the form `s / τ_ρ^e` for some `e` and some
   section `s` of the `e`-th power.
4. Multiplying by powers of `τ_ρ` shows that the images increase with `m`.
5. Steinberg's theorem supplies irreducibility of the first factor.
6. Both factors have dimension `p^(s·N)`, with `N` the number of positive roots,
   so they can be put on the same `Fin m`.

None of these structures (Borel subgroups, flag varieties, line bundles,
highest-weight modules) is asserted by this statement.
