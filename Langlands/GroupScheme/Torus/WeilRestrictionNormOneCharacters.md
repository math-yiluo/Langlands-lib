# Actual norm-one characters as the quotient embedding lattice

This internal construction identifies the character group of the actual norm-one torus with the integer embedding lattice modulo constant vectors. Its cocharacter group is the previously constructed sum-zero embedding lattice. The construction retains the actual norm kernel, its actual inclusion into the Weil restriction, and the ordinary Galois actions on actual group-scheme morphisms.

For the field comparison, Lean assumes fields `k`, `K`, and `Ω`, algebra structures of `K` and `Ω` over `k`, finite dimensionality and separability of `K/k`, and that every minimal polynomial of an element of `K` splits after mapping its coefficients to `Ω`. It requires neither normality of `K/k` nor a Galois hypothesis on `Ω/k`. The ordinary action uses the full group of `k`-algebra automorphisms of `Ω`.

## Actual restriction and perfectness

`characterLattice.precompose` restricts actual characters along an actual commutative-group-scheme morphism over any base scheme. Its transport and ordinary Galois naturality laws follow from the all-test descent-point formula and naturality of descent points under base-changed morphisms.

`latticePairing_isPerfPair_of_split` transfers perfectness of the actual lattice pairing along an actual split-torus isomorphism. Applied to the proved splitting of the norm-one kernel, it proves `normOne_latticePairing_isPerfPair`. The nonempty embedding type needed to choose a deleted coordinate follows from the finite-separable splitting hypotheses.

`normOneEmbeddingCharacterRestriction` first converts an integer function on the embeddings into the actual ambient Weil-restriction character and then precomposes with the actual base-changed norm-one inclusion. Its pairing with an actual norm-one cocharacter is the dot product with that cocharacter's sum-zero embedding coordinates. This is an equality for the actual lattice pairing, not an assumed lattice exactness statement.

## Integral exactness and quotient

`embeddingSumZeroDualRestriction` restricts the standard integer dot product to the sum-zero submodule. Given an embedding `τ₀`, `embeddingSumZeroProjection` sends an ambient vector `m` to `m` minus the singleton vector at `τ₀` with coefficient equal to the total sum of `m`. It retracts the sum-zero submodule. Composing any integral functional with this projection extends it to the ambient lattice, so dot-product restriction is surjective. This uses no division by the extension degree.

`normOneCharacterDualEquiv` combines actual perfectness with the actual cocharacter comparison to identify actual characters with these integral functionals. Under this equivalence, actual character restriction is exactly dot-product restriction. Consequently actual restriction is surjective.

`embeddingDiagonal` is the range of the constant-vector linear map from the integers. An embedding vector annihilates the sum-zero lattice exactly when it belongs to this diagonal: evaluating on the difference of the singleton vectors at `τ` and `τ₀` forces every coordinate to equal the coordinate at `τ₀`; constant vectors annihilate sum-zero vectors by distributivity. Perfectness transfers this kernel calculation to actual character restriction.

The first isomorphism theorem gives `embeddingQuotientNormOneCharacterEquiv` from the quotient by the diagonal to actual norm-one characters. Its inverse is `normOneSeparableEmbeddingCharacterEquiv`, the canonical quotient-coordinate comparison. The auxiliary choice of embedding used to prove surjectivity and the kernel equality is absent from these final maps, which are induced by actual restriction.

## Pairing, points, and Galois action

For a representative `m` of a quotient class and a sum-zero vector `n`, `normOne_embedding_latticePairing` identifies the actual pairing of their inverse images with the sum of `m τ * n τ` over the embeddings. The previously proved actual perfectness applies to this pairing.

The inverse image of the quotient class of `m` is precisely the actual ambient character associated to `m`, restricted along the inclusion. `normOneSeparableEmbeddingCharacterEquiv_symm_points` proves on every test scheme that its value is the monomial with exponents `m τ` in the included point's embedding coordinates. Arbitrary, including nonreduced, test schemes are retained.

`embeddingQuotientRepresentation` is the representation induced on the quotient by the ambient inverse-pullback permutation action. Constant vectors are preserved. Actual Galois transport commutes with restriction, by general restriction naturality and the proved ambient character action formula. Surjectivity of actual restriction then proves that `normOneSeparableEmbeddingCharacterEquiv` intertwines the ordinary actual Galois action with this quotient representation.

## Provenance and scope

These are internal constructions from the published actual norm-one splitting, the actual sum-zero cocharacter comparison, perfect lattice pairings of split tori, and Mathlib's integral dot-product, dual-map, quotient, and representation constructions. No external structural assertion, assumed character exactness, smoothness argument, or field-point approximation is used. The Lean proof route is the integral retraction and perfectness argument described above.

This unit does not prove general rational-point descent, continuity of the norm-one lattice actions, or the whole algebraic-group program's acceptance conditions. It supplies the actual norm-one character quotient, its perfect pairing with sum-zero cocharacters, its all-test monomial formula, and its ordinary Galois compatibility.
