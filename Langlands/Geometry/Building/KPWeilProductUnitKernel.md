# Character kernels for products of Weil restrictions

Authors: Worker 706 and Worker 1587.

All declarations are in `Langlands.GroupScheme.WeilGm`. The fields and finite
index types retain the arbitrary universe `u`; valuation groups may lie in
other universes. This is a supporting construction for the induced-torus
Iwahori proof.

For fields `k` and `L` with `Algebra k L`, let `B` be a commutative `k`-algebra
finite projective as a `k`-module. Given a finite type `J` and an algebra
splitting

```text
e : L ⊗[k] B ≃ₐ[L] (J → L),
```

`decomposition_rational_coordinate` proves that the actual rational-point
splitting `commDecompositionIso` applies the direct tensor map
`B ⊗[k] L → L ⊗[k] B → (J → L)` to `extensionUnitsEquiv k L B x`.
Its coordinate at `j` is read using `MulEquiv.piUnits`.

`mem_decomposition_characterValuationKernel` therefore identifies the kernel
of any valuation of `L` on the base-changed Weil restriction with the points
whose direct tensor coordinates all have valuation one.

Now let `L/k` be finite Galois, let `I` be finite with decidable equality,
and let `E : I → IntermediateField k L`. Put `B = ∏ i, E i`.
The imported `Torus/WeilRestrictionProductDecomposition` pair provides the
unchanged `productEmbeddingDecomposition`, which splits `L ⊗[k] B` by first distributing the
tensor product over `i`, then applying the canonical finite-separable
embedding decomposition to each factor. `productEmbeddingUncurry` combines
the two coordinate indices into the finite sigma type `Σ i, E i →ₐ[k] L`.
`productEmbeddingDecomposition_units` verifies that these coordinates are
exactly the existing `productTensorEmbeddingUnitsEquiv k L E` coordinates.

The main criterion is

```text
mem_product_extension_characterValuationKernel :
  x ∈ characterValuationKernel v (Res_{B/k} Gm)_L ↔
    ∀ i τ,
      v (productTensorEmbeddingUnitsEquiv k L E
        (extensionUnitsEquiv k L B x) i τ) = 1.
```

`productTensorEmbeddingUnitsEquiv_includeLeft` shows that extending a unit
of `B` gives the embedding values `τ(z_i)` in these coordinates.
Finally, `product_coordinate_valuation_eq_one_of_mem` assumes valuations
`vk`, `vL`, an extension `vk.HasExtension vL`, and Galois invariance of `vL`.
For a point `x` in the ground-field character kernel, it proves

```text
vL (algebraMap (E i) L
  (MulEquiv.piUnits (rationalUnitsEquiv k B x) i)) = 1
```

for each `i`. The finite Galois kernel-ascent theorem first places the
extended point in the kernel over `L`; the product criterion is then applied
at the inclusion embedding `(E i).val`.

The generic coordinate bridge follows the same implemented route as the
single-field bridge in `KPWeilRestrictionUnitKernel`: pass to coefficient
points on `Spec L`, use the all-test splitting formula, and transport global
sections to `L` with `Corepresented.affineSectionsIso`. Tensor induction proves
compatibility with the supplied algebra decomposition. In the pure-tensor case,
the algebra equivalence's `L`-linearity identifies evaluation of `l ⊗ b`
with `l` times evaluation of `1 ⊗ b`. The generic kernel criterion follows
from the split-torus coordinate criterion and functoriality along the splitting
and its inverse. The product specialization merely identifies the finite
coordinate types; it adds no new norm or surjectivity assertion.

Provenance: an internal deduction from the published Weil-restriction
decomposition, relative-spectrum adjunction and character-kernel
functoriality. Worker 1587 supplied the direct point interfaces and shared
product embedding coordinates; Worker 706 proved their comparisons with
the actual character-valuation kernels.
