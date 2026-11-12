# Canonical Galois compatibility of the original Weil-product comparison

Author: Worker 166. Internal derivation from actual coordinate morphisms,
canonical product transport and pullback evaluation coherence.

For fields `k`, `E`, and `L` with the given algebra structures and a finite
embedding index, `EmbeddingProduct.evaluation_product_descent` applies to any
original `k`-group `W`, `E`-group `H`, evaluation map `e : W_E → H`, and map
`f : W_L → pi (family H)` whose coordinates are the actual pullbacks of `e`.
For each `k`-automorphism `σ` of `L`, it proves that `f` commutes with canonical
descent on `W_L` and the published `EmbeddingProduct.galoisIso` on the product.
No Galois-extension hypothesis is required for this individual-automorphism
identity.

The proof uses product extensionality. Each target embedding is written as
`embeddingEquiv σ τ` by surjectivity of that permutation. The published
`galoisIso_hom_π` identifies that coordinate with the pulled-back original
projection followed by the direct/iterated scalar-extension comparison.
Functoriality and the supplied coordinate formulas then reduce the equality to
`evaluationComponent_descent`, the actual pullback coherence theorem.

`AffineWeil.embeddingProductIsoOfBijective_descent` specializes this result to
the published `embeddingProductIsoOfBijective`, using the coordinate-morphism
identity from `AffineWeilEmbeddingCoordinateMorphism`. Here `E/k` is finite
dimensional, `H` is affine and locally of finite type, and the canonical tensor
embedding evaluation is assumed bijective, as required for that original
isomorphism. The morphism `e` is exactly `AffineWeil.evaluation k E H`.

The product's Galois transport is the previously and independently defined map
built from original pullback comparisons and the embedding permutation. The
proof establishes compatibility with that transport; it is not defined by
conjugating canonical descent through the Weil-product comparison.
