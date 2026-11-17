# Tensor products and actual central simple algebra constructors

For every field `K`, this module constructs actual central simple algebras from
tensor products, multiplicative opposites, scalar extensions and positive-size
matrix algebras. The ground field, each algebra and the extension field have
independent universes. In particular, setting all universes equal gives
`K : Type u` and algebras in `Type u` for every `u`. All characteristics,
including imperfect fields of characteristic two, are retained.

## Constructors

The namespace `Langlands.Brauer` provides:

- `groundField K : CSA K`, with carrier `K`;
- `tensor A B`, with carrier `A ⊗[K] B`;
- `opposite A`, with carrier `Aᵐᵒᵖ`;
- `baseChange L A`, with carrier `L ⊗[K] A`, for any field extension `L/K`;
- `matrix A n`, with carrier `Matrix (Fin n) (Fin n) A`, for `[NeZero n]`.

These are Mathlib's `CSA` objects, with their existing algebra structures and
proved centrality, simplicity and finite dimensionality. They carry no assumed
group laws. This unit supplies representative algebras; quotient operations
and scalar-extension functoriality are subsequent units.

## Canonical enveloping equivalences

The namespace `Langlands.CentralSimple` first strengthens the published
`mulLeftRight_surjective K A`: `envelopingEquiv K A` is an algebra equivalence
from `A ⊗[K] Aᵐᵒᵖ` to `Module.End K A`, for a finite-dimensional central simple
algebra `A`. Its underlying homomorphism is exactly `AlgHom.mulLeftRight K A`,
which sends `a ⊗ op b` to the operator `x ↦ a*x*b`. Surjectivity is the
published density proof; injectivity follows because the source and target
have equal finite dimensions. The opposite has the same vector-space dimension
as `A` by `MulOpposite.opLinearEquiv`.

`endTensorEquiv K A B` is the natural algebra equivalence
`End_K(A) ⊗ End_K(B) ≃ End_K(A ⊗ B)` for finite-dimensional vector spaces,
implemented using Mathlib's tensor-Hom linear equivalence. On pure tensors
it sends `f ⊗ g` to `a ⊗ b ↦ f(a) ⊗ g(b)`.

`tensorEnvelopingEquiv K A B` distributes the opposite over the tensor product,
shuffles the four factors into `(A ⊗ Aᵐᵒᵖ) ⊗ (B ⊗ Bᵐᵒᵖ)`, applies both
enveloping equivalences and then `endTensorEquiv`. The theorem
`tensorEnvelopingEquiv_toAlgHom` proves that this composite is exactly
`AlgHom.mulLeftRight K (A ⊗[K] B)`.

Two internal converse arguments explain why this proves tensor closure.
`isSimpleRing_of_enveloping_surjective` takes a nonzero element of a nonzero
two-sided ideal and a linear functional taking that element to one. Surjectivity
realizes the map `x ↦ f(x)*1` by a two-sided multiplication operator. Every such
operator preserves the ideal, so the ideal contains one.
`isCentral_of_enveloping_surjective` chooses a linear functional taking one to
one. A central element `z` satisfies `T(z)=T(1)*z` for every two-sided
multiplication operator `T`; applying the selected scalar-valued projection
shows that `z` is a scalar. Both results assume nontriviality of the algebra,
as well as the stated surjectivity.

Consequently `isSimpleRing_tensor` and `isCentral_tensor` prove closure for
the actual tensor algebra. Its nontriviality follows from flatness over `K`
and injectivity of the algebra map. Finite dimensionality, the opposite and
matrix closure instances come from Mathlib. Scalar-extension closure comes
from the published `CentralSimpleScalarExtension` module.

## Source and provenance

The original source is Knus–Merkurjev–Rost–Tignol, *The Book of Involutions*
(1998), §1, printed pp.3–4 / PDF pp.26–27, registered as
`knus-merkurjev-rost-tignol-1998-book-of-involutions`, content SHA256
`e21641aeb1425b63bec70032352f0cb33275f7bd1ddf682c3bea62b798654fe0`.
Page 3 defines scalar extension and the opposite and states Wedderburn
Theorem (1.1), including the canonical enveloping equivalence. Page 4,
following Brauer equivalence Definition (1.3), states the tensor-product group
construction, which entails closure of central simple algebras under tensor
products. Both original pages were read. The retained official author errata
and the page-sorted comments, snapshot 13 November 2026, have no correction
to these pages.

The factor-by-factor tensor proof and the two surjectivity converse lemmas are
internal derivations of these facts. Their route uses the already published
density argument before tensor closure, rather than assuming splitting or a
Brauer-group structure. No local-field, cohomological, Tits-index, or
characteristic restriction is used.
