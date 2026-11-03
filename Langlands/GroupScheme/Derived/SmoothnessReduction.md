# Reduction of derived-subgroup smoothness to reduced-source generation

`derivedSubgroupSmoothness_of_reducedImageGeneration` is an internal
proof-producing definition giving a conditional deduction from the existing geometric and subgroup APIs. Its
explicit input is a proof of
`GeometricallyReducedAffineImageGenerationStatement`; its conclusion is the
exact `DerivedSubgroupSmoothnessStatement` in arbitrary universe `u`. It does
not supply the input proof or assert the unconditional smoothness target.

For a smooth affine locally finite type group `G` over an arbitrary field,
the actual product scheme `G.X ⊗ G.X` is affine and smooth. These properties
follow from stability under base change and composition, since its structure
morphism is the first pullback projection followed by `G`'s structure morphism.
Smoothness also supplies local finite type. The published
`Langlands.AlgebraicGeometry.smoothGeometricallyReduced` theorem gives geometric
reducedness of this product, without a connectedness assumption.

The supplied generation proof applies to the actual commutator morphism
`commutatorMap (𝟙 G) (𝟙 G)` and gives a smooth representative of its fixed
closed image envelope. The comparison and uniqueness construction in
`Derived.CommutatorEnvelope` then transports smoothness to the original
arbitrary derived-subgroup inclusion `d : D ⟶ G`.

The proof retains the original field and universe and uses the equality of
subgroup functors on all test schemes. No rational-point generation,
separability, perfectness, connectedness, or characteristic restriction enters.
The construction of the smooth generated representative remains the separate
geometric proof obligation.
