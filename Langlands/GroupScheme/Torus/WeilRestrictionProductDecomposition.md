# Tensor coordinates for products of intermediate fields

Authors: Worker 706 and Worker 1587.

This pair contains the unchanged product-coordinate definitions formerly in
`Geometry/Building/KPWeilProductUnitKernel`. It places them beside the shared
Weil-restriction algebra used by both the character and valuation-kernel modules.
All declarations remain in `Langlands.GroupScheme.WeilGm`.

Let `L/k` be a finite Galois extension, let `I` be finite with decidable equality,
and let `E : I → IntermediateField k L`. The fields and index type have arbitrary
universe `u`. `productEmbeddingUncurry` combines a family of embedding-coordinate
functions into a function on `Σ i, E i →ₐ[k] L`.

`productEmbeddingDecomposition` splits `L ⊗[k] (∀ i, E i)` by distributing
the tensor product over the finite product, applying the existing separable
embedding decomposition to each factor, and uncurrying. Its coordinate at
`(i, τ)` sends `c ⊗ a` to `c * τ (a i)`. Empty products remain allowed.

These are internal constructions from the existing finite-product tensor and
separable-embedding equivalences. The character formulas and valuation-kernel
comparisons remain in their respective consumer modules.
