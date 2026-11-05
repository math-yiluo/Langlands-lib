# Transport of affine Weyl groups

This is an internal, derived construction supporting comparisons between apartments.
It uses the affine reflections and affine Weyl groups already defined in
`Langlands.Geometry.Building.AffineRootSystem`. It does not assert existence of a
comparison between apartments belonging to different groups.

For arbitrary real affine spaces `A` and `B`, with independently sized vector and
point universes, an affine equivalence `e : A ≃ᵃ[ℝ] B` transports an affine
functional `ψ` to `ψ ∘ e⁻¹`. The definition `affineFunctionalTransport` is the
corresponding linear equivalence of spaces of affine functionals, and
`transportedRoots e Ψ` is the image of the set `Ψ` under this equivalence.
The definition `affineConjugation` sends an affine automorphism `g` of `A` to
`e ∘ g ∘ e⁻¹` and is an isomorphism of the automorphism groups.

The theorem `isCoroot_transport_iff` identifies coroots under the linear part of
`e`. The derivative pairing is unchanged, and inverse precomposition takes
`η - η.linear v • ψ` to the corresponding expression for the transported roots.
Injectivity of the functional transport gives the reverse implication.

The theorem `affineConjugation_reflection` follows by evaluating on a point and
using the affine map law for vector addition and the linear map law for scalar
multiplication. The theorem `map_affineWeylGroup` then proves that conjugation
maps `affineWeylGroup Ψ` onto `affineWeylGroup (transportedRoots e Ψ)`.
The proof uses preservation of subgroup closure under group homomorphisms and
identifies the two sets of reflection generators. A target coroot vector is
pulled back by `e.linear.symm` for the reverse inclusion.
The final theorem substitutes a supplied equality of root sets into this result.

These are algebraic consequences of the existing definitions, with no new
literature claims or additional affine root system axioms. In particular the
comparison applies to any set of affine functionals, including the empty set.
