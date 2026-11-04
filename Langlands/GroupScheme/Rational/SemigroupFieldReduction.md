# Field-extension detection of exact ordered semigroup products

This internal reduction combines the actual character, action-weight, semigroup
subgroup and ordered-multiplication base-change comparisons. The fields occupy
an arbitrary common universe.

`weightBlocksBaseChange b S Ψ` takes the image of each block under actual
character pullback and retains its index. Its membership formula is an image
witness, its union is the image of the original union, and the positive closure
of each image is the image of the original positive closure. There is no added
zero and no change to the multiplication order. The block index has an
independent universe.

For a split acting torus, character pullback is bijective. The comparison of
individual external-action weight spaces identifies the entire occurring
support with its image, including an occurring zero. Thus a covering by blocks
remains a covering after any field extension. Injectivity of character pullback
preserves disjointness and the exact block-versus-positive-closure exclusion.
Disjointness of different positive closures is never required.

`HasOrderedSemigroupProducts.of_fieldExtension` assumes that the actual
pulled-back action has the ordered-product property. The ambient group over
the original field is affine, smooth and locally of finite type, and the acting
torus is split. Apply the assumed property to the transported blocks. Choose
smooth connected closed representatives of the original semigroup subgroup
functors by the published geometric realization theorem. The semigroup
base-change comparison identifies their pulled-back inclusions as
representatives of the transported factors. The published independence of
ordered multiplication from a choice of representative gives invertibility of
the ordered multiplication for these pulled-back original factors. Field
extension detects whether the original scheme morphism is an isomorphism.
The result therefore supplies the original factors and the original
ordered-multiplication isomorphism, including the empty product. It requires
neither solvability nor connectedness of the ambient group.

`semigroupOrderedProduct_of_algebraicallyClosed` applies this reduction to an
algebraic closure in the same universe. The original smooth affine connected
group remains so, using geometric connectedness for connectedness. Uniform
all-test solvability persists with its original derived-series bound. Hence a
proof of the exact assertion for every algebraically closed solvable group in
that universe implies the existing `SemigroupOrderedProductStatement` over all
fields in that universe.

These results are derived from published geometric realization, representative
comparison and solvability transport, together with the actual base-change
comparisons. They do not prove the remaining algebraically closed solvable
case, construct a compatible torus and unipotent decomposition, or remove the
structural premises from the conditional unipotent induction.
