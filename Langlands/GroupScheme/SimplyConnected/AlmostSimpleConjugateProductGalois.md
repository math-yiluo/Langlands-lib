# Canonical Galois compatibility of the actual conjugate-factor product

Worker 166. This is internal supporting content for the simply connected
almost-simple Weil-restriction structure theorem. It derives explicit
coherence identities from the published actual product, factor-inclusion and
pullback-comparison constructions. It makes no new source assertion.

For fields `k`, `E`, and `L` in arbitrary `Type u`, with `k`-algebra structures
on `E` and `L` and finitely many `k`-embeddings `E →ₐ[k] L`, let `H` be any
actual group scheme over `Spec E`. No commutativity, affineness, smoothness or
finite-type hypothesis is needed for the following construction.
`EmbeddingProduct.family H τ` is the actual scalar extension of `H` along
`τ`. For each `k`-automorphism `σ` of `L`, `embeddingEquiv σ` is composition
`τ ↦ σ ∘ τ`. The isomorphism `coordinateIso H σ τ` compares the iterated
pullback along `τ` and `σ` with the direct pullback along `σ ∘ τ`.

`EmbeddingProduct.galoisIso H σ` is an actual isomorphism from the pullback
of the product of these scalar extensions to the same product. It is built
from preservation of finite products by base change, the coordinate
comparisons and reindexing by `embeddingEquiv σ`.
`galoisIso_hom_π` proves its exact original-coordinate projection formula:
the projection at `σ ∘ τ` after transport is the pullback of the original
projection at `τ`, followed by `coordinateIso H σ τ`.
`map_inclusion_galoisIso` proves the corresponding equality on each original
factor insertion. These are identities of actual group-scheme homomorphisms.
The unit does not bundle or assert a separate cocycle-law theorem.

The finite-product helpers apply to noncommutative groups. On every test
scheme, `piPointsEquiv_piFactorInclusionHom` identifies an insertion with
`Pi.mulSingle`. The noncommutative finite-product extensionality theorem
`MonoidHom.pi_ext` then proves `pi_hom_ext_of_factorInclusion`: restrictions
to all original factor insertions determine an outgoing homomorphism.
`baseChange_trivialHom` and `baseChange_piFactorInclusionHom` prove that
pullback respects the identity-valued homomorphisms and the original
insertions through the product comparison. Coordinate isomorphisms and
reindexing also preserve insertions, as expressed by
`piFactorInclusionHom_mapIso`, `piFactorInclusionHom_reindex` and their
combined form `piFactorInclusionHom_comparison`.
`baseChange_pi_hom_ext` consequently lets one test outgoing homomorphisms
from the actual pullback product on the pulled-back original insertions.

For the application, take fields `k` and `L` in `Type u`, an arbitrary Galois
extension `L/k`, and an actual group scheme `G` over `Spec k`. Assume that
`G` is affine, quasi-compact, quasi-separated and locally of finite
presentation, and that its scalar extension to `L` is smooth and affine.
Let `D` be a supplied `SimplyConnectedAlmostSimpleProduct` presentation of
that scalar extension. Use its exact stabilizer field
`E = D.factorStabilizerField i` and actual descended factor
`H = (D.factorStabilizerDescent i).1`.

If `G` is almost-simple, `embeddingConjugateProductIso_inclusion` proves that
the published actual product isomorphism
`q = D.embeddingConjugateProductIso hG i` carries every original embedding
factor insertion to `D.embeddingFactorInclusion i τ`. This follows from the
generic product-inclusion comparison and the published exact recovery of
the conjugate-factor inclusion.

`embeddingFactorInclusion_descent` proves, without using almost-simplicity
of `G`, that pulling back each embedding inclusion and then applying the
canonical descent of `G_L` agrees with the coordinate comparison followed
by the inclusion at `σ ∘ τ`. Its proof uses
`comparison_descent_coherence` for the ambient iterated/direct pullback
comparisons, followed by `Descent.pullbackComparison_naturality` for the
actual descended factor inclusion.

Finally, `embeddingConjugateProductIso_descent` proves for every `σ` the
exact identity

```text
baseChange(σ).map(q.hom) ≫ canonicalDescent(G, σ).hom
  = (EmbeddingProduct.galoisIso H σ).hom ≫ q.hom.
```

The proof tests both sides on the pulled-back original factor insertions,
uses the two inclusion identities above, and applies the independently
constructed embedding-product transport formula. The transport on the
right is defined from `H`, the actual embeddings and canonical pullback
comparisons; its definition does not use `q` or the product presentation.

This unit proves the canonical compatibility of the actual conjugate-factor
product. It does not construct the embedding-product splitting of
`AffineWeil.groupScheme`, prove that almost-simple groups over a separably
closed field are absolutely almost-simple, or prove
`SimplyConnectedAlmostSimpleWeilRestrictionStatement`.
