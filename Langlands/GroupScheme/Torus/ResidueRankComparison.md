# Ranks of closed split tori against a maximal torus of a residue fibre

This is an internal derivation from published Library results. It is a helper for the
proof of `Langlands.Geometry.Building.SpecialTorusExistenceStatement` (Kaletha–Prasad,
Proposition 9.3.4). It compares the rank of a torus lifting a maximal torus of the special fibre
with the rank of a maximal split torus over the maximal unramified extension. The module makes
no independent literature assertion.

`card_le_card_of_isMaximalTorus`: let `k` be algebraically closed and `H` a smooth connected
affine group over `Spec k`. Let `j : T ⟶ H` be a maximal torus with `T ≅ splitTorus I`, and
`a : A ⟶ H` a closed subgroup with `A ≅ splitTorus J` (`I`, `J` finite). Then
`Nat.card J ≤ Nat.card I`. The proof puts `A` inside a maximal torus `T'` of `H`
(`EnvelopeInfiniteReduction.exists_isMaximalTorus_factor`) through a factorization `f`.
`maximalTorusConjugacy` gives an isomorphism `φ : T' ≅ T`. Since `a` is a closed immersion, `f`
is a monomorphism. So the composite `splitTorus J ≅ A ⟶ T' ≅ T ≅ splitTorus I` is a monomorphism,
and `splitTorus.card_le_card_of_mono` gives the inequality.

`baseChangeSquareIso`: for a commutative square `γ ≫ s = s' ≫ β` of base schemes, the iterated
base changes `(G_s)_γ` and `(G_β)_{s'}` of a group scheme `G` are isomorphic. The isomorphism
composes two instances of `baseChangeCompIso` with the transport along the equality of the
composites.

`card_le_card_of_residue_isMaximalTorus`: let `M` be a smooth affine group over `Spec O`, and
`s : Spec k ⟶ Spec O` a field point whose fibre `M_k` is connected. Let `t₀ : T₀ ⟶ M_k` be a
closed maximal torus. Let `𝒯` be a group over `Spec O` with an isomorphism
`e : 𝒯_k ≅ T₀`. Take a base change `β : Spec O' ⟶ Spec O` and a point `s' : Spec k' ⟶ Spec O'`
with `k'` an algebraically closed extension of `k`, such that
`Spec k' ⟶ Spec k ⟶ Spec O` equals `s' ≫ β`. Suppose `𝒯_{O'} ≅ splitTorus I`. Then every
closed subgroup `a : 𝒜 ⟶ M_{O'}` with `𝒜 ≅ splitTorus J` satisfies `Nat.card J ≤ Nat.card I`.

The proof works in `H := (M_k)_{k'}`. This group is smooth and affine, and it is connected by
`connectedSpace_baseChange_of_smooth_affine`. `maximalTorusBaseChange` makes `(t₀)_{k'}` a
maximal torus of `H`. The base change `a_{s'}`, transported along `baseChangeSquareIso`, is a
closed subgroup of `H` (`IsClosedSubgroup.baseChange`, `comp_iso`). The two splittings come from
the chain `(T₀)_{k'} ≅ (𝒯_k)_{k'} ≅ (𝒯_{O'})_{k'} ≅ splitTorus I`, built from `e`,
`baseChangeSquareIso`, `eT` and `splitTorus.baseChangeIso`, and from
`𝒜_{k'} ≅ splitTorus J`. The first theorem then gives the inequality.
