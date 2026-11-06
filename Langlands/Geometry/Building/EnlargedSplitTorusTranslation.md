# Actual reduced translation embeddings into an enlarged split torus

This internal construction first treats two supplied split commutative group
schemes over one field, a homomorphism between them, and compatible maps into
one affine group locally of finite type. The actual adjoint-root restriction
theorem identifies the full preimage of the ambient common root kernel with
the source root kernel. Ambient roots restricting to zero contribute zero
evaluation; every source root lifts to a nonzero ambient root restriction.
The actual real cocharacter map therefore descends to an injective linear map
on reduced translation spaces. No root bijection, central isogeny or
monomorphism hypothesis on the torus map is required. Each nonzero restricted
root intertwines the existing reduced root forms.

For an arbitrary field extension and an actual original split subtorus,
fieldExtensionTranslationEmbedding constructs an actual maximal split torus
upstairs containing its scheme pullback. It reuses the published
maximalSplitExtension construction after proving splitness and closedness of
the pulled-back subtorus. Composing actual split-torus field extension on
reduced translations with the preceding injective map gives an injection from
the original reduced translation space. The output records the actual torus,
its maximality, factorization, linear map, injectivity, and its representative
formula. It assumes no reductivity, smoothness, Galois structure or chosen
upstairs torus.

The provenance is internal: the published actual cocharacter map and pairing,
exact weight restriction, maximal split-torus enlargement, and quotient
universal property give the construction. No new original-literature assertion
is added. This is a linear translation-space comparison, with no affine origin
chosen. Galois stability, compatible root valuations, an affine apartment map,
sharp-fixer comparison, special points and the supplied-model building
comparison remain separate obligations.
