# Specialization of diagonalizable homomorphisms

For a field `k : Type u` that is algebraically closed, an affine group scheme `G`
over `k` locally of finite type, and any additive commutative group `Λ : Type u`,
`DiagonalizableHomVanishingBaseChangeStatement.{u}` says: if every actual group
scheme homomorphism `D_k(Λ) → G` is zero, then every homomorphism
`D_K(Λ) → G_K` is zero for every extension field `K : Type u` of `k`.
The theorem `diagonalizableHomVanishingBaseChange` proves this proposition.
Neither smoothness, connectedness nor commutativity of `G` is required.
There is no restriction on the characteristic or on `Λ`.

The construction generalizes the published `CocharacterDatum` multiplicative-point
construction to arbitrary affine targets. A multiplicative point over `k[Λ]`
defines a homomorphism from `D_k(Λ)` by specializing its universal parameter.
Multiplication and naturality on all commutative test algebras give the actual
homomorphism by corepresentation. Its universal image point recovers the original
point. Conversely, the universal image of every actual homomorphism is
multiplicative, using postcomposition and multiplicativity of the identity point
of the diagonalizable group.

A multiplicative point over `K[Λ]` descends, with its coefficient extension
equation, to a finitely generated `k`-subalgebra `B` of `K`: take the coefficients
of the images of finitely many coordinate algebra generators. Injectivity of
coefficient extension reflects multiplicativity. Since `B` is a domain, a maximal
ideal and Zariski's lemma give a `k`-algebra specialization `B → k`. The published
`CentralSurjectionImage.IsMultG.eq_one_of_isDomain` rigidity theorem says that a
multiplicative point over `B[Λ]` whose specialization is trivial is itself trivial.
The base-field hypothesis kills every specialized point through its reconstructed
diagonalizable homomorphism. Extending coefficients back therefore kills the
original point.

The actual affine-point equivalence for scheme pullback commutes with exponent
maps and multiplication, so it preserves and reflects multiplicativity. Apply it
to the universal image of a homomorphism over `K` and use the preceding vanishing
to prove that homomorphism is zero. The corollary
`CocharacterSpecialization.gm_hom_eq_zero_of_baseField` uses the published
isomorphism between `Gm` and the diagonalizable group of the exponent lattice
`PUnit → ℤ` to obtain the same result for cocharacters.

This is an internal deduction from the published coordinate, coefficient descent,
corepresentation, pullback and rigidity results. It adds no structural
classification input. It is a supporting result for the no-torus unipotence
problem and does not itself conclude unipotence.
