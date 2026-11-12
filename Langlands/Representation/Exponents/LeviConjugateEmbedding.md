# Conjugate represented inducing data and embeddings

Original transport construction: Worker 1281.

Internal support for point 3 of Renard VI.5.4 Corollary, printed p.175 /
PDF p.181 of Renard's 2026 edition. This is a derived transport argument,
using the published normalized Jacquet conjugation equivalence and represented
Frobenius reciprocity. It does not supply the association theorem or the
unconditional same-Levi corollary.

The published source-presentation lemmas in
`ArbitraryParabolicLeviReparametrization` express subgroup multiplication as
composition with a product isomorphism. This module reuses
`isIso_subgroupMultiplication_iso_comp` to retain the specified multiplication
isomorphism, `pointImage_iso_comp` to preserve the literal point image, and
`IsRationalLeviSubgroup.iso_comp` to transport rational Levi structure.
The duplicate helper declarations have been removed.

`leviJacquetConjugatePresentationEquiv` combines this source change with
ambient conjugation. If the original parabolic inclusion is `p`, its Levi
inclusion is `l : M' → P`, `e : M ≅ M'`, and `g ∈ G(k)`, then the new
inclusion is `p ≫ innerIso g`, with Levi inclusion `e.hom ≫ l`. The new
normalized Jacquet representation of `M(k)` is equivalent to the original
Jacquet representation restricted through the actual point map of `e`.
The map on the actual coinvariant quotient is translation by `π(g)`.
The proof checks literal radical and Levi images and then invokes the
published conjugation equivalence, including its Haar-modulus comparison.

`exists_embedding_conjugate_presentation` assumes an equivariant linear
equivalence from `ρ` to `ρ'` restricted through `e` and an embedding of an
irreducible `σ` into the original normalized induction of `ρ'`. Frobenius
reciprocity takes that embedding to a nonzero map from the original Jacquet
module to `ρ'`. Restricting the action, composing with the inverse Jacquet
equivalence, and composing with the inverse inducing equivalence gives a
nonzero map from the new Jacquet module to `ρ`. Inverse Frobenius gives a
nonzero map into the new induction; irreducibility of `σ` makes it injective.
The field and three carrier universes remain independent. No supercuspidality,
admissibility, or finite-length assumption is needed for this transport.

`exists_parabolic_embedding_of_associated` adds the actual association equation
`e.hom ≫ l ≫ p = j ≫ innerIso g`. Applying the embedding transport with `g⁻¹`
gives an actual parabolic with Levi source `M` whose composite inclusion is
exactly `j`. The proof cancels the inner isomorphism with its inverse and
bundles the resulting injective intertwiner as a smooth-category morphism.
The input embedding may involve an inducing carrier in a different universe.
