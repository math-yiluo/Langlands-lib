# Affine morphism descent detected by a dominant parametrization

This is an internal, derived construction. It applies
`Langlands.TensorEmbeddingDescent` to the actual coordinate algebras of affine
schemes. It is infrastructure for descending geometric characters in the split
geometric radical argument; it makes no direct assertion from the literature.

Let `k : Type u` be a field, and let `K : Type u` be any nontrivial commutative
`k`-algebra. Let `T`, `X`, and `Y` be affine schemes over `Spec k`. Suppose
`p : T → X` is schematically dominant and quasi-compact. Write `F(X)` for the
actual pullback of `X` to `Spec K`, regarded again over `Spec k`, and write
`π_X : F(X) → X` for its projection.

For morphisms `g : F(X) → Y` and `h : T → Y` satisfying
`F(p) ≫ g = π_T ≫ h`, `existsUnique_hom` proves that there is a unique actual
morphism `g₀ : X → Y` with `π_X ≫ g₀ = g`. The definition `descendHom` chooses
that morphism. `projection_comp_descendHom` proves its recovery equality,
and `descendHom_unique` proves the corresponding uniqueness property. No
finite-type, smoothness, separability, algebraicity or perfection assumption is
made. All schemes and algebras here have the single common carrier universe `u`.

The proof first establishes `existsUnique_specHom` for spectra in tensor
coordinates, using the full faithfulness of `algSpec` to transfer the given
scheme-map equality to an algebra-map equality. It applies unique algebra-map
descent from `TensorEmbeddingDescent` and transfers back by spectrum. For
arbitrary affine schemes, `affineSpectrumIso` is their canonical coordinate
presentation. Scheme-theoretic dominance and quasi-compactness make the
coordinate pullback injective. `tensorModelIso` and `affineModelIso` identify the
actual scalar extension with its tensor spectrum, with naturality and projection
identities derived from the existing `PointTopology` spectrum comparisons.
Transport through these isomorphisms proves existence and uniqueness for the
original schemes and their actual projections.

This construction descends morphisms of schemes over the ground field. Group
homomorphism descent, character descent, construction of a torus quotient, and
its unipotent kernel and radical geometry remain separate obligations.
