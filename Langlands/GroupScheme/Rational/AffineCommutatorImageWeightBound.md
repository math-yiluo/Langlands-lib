# Literal augmentation weight bound for the actual commutator image

This internal application proves an augmentation-coordinate weight bound for
the actual closed commutator image. Let `k : Type u` be any field, let `S`
be a commutative group scheme, and let `G`, `H`, and `K` be affine group
schemes with actual automorphic `S`-actions. Suppose the homomorphisms
`i : H ⟶ G` and `j : K ⟶ G` respect these actions on every test scheme.
No smoothness, connectedness, reducedness or finite-type hypothesis is needed
for this coordinate-image calculation.

The canonical augmentation pullback from the preceding module is injective:
including its tensor value recovers the actual coordinate pullback, which is
already proved injective. `imageAugmentationRangeEquiv` therefore identifies
the actual image augmentation with its range in the tensor of the two input
augmentation kernels.

`image_support_subset_sum_of_decompositions` first records the bound under
three explicit internal direct-sum hypotheses: the two input augmentation
decompositions and the coordinate decomposition of their actual product.
The proof applies the generic constant-slice support theorem to the actual
product-to-image factor. Its pointed equivariance, injectivity and two
constant-slice identities are the actual identities proved in
`AffineCommutatorImageSupport`. The group specializations of pointed support
then identify the two input supports with `CoordinateWeights.support`.

`image_support_subset_sum` uses the published
`pointedCoordinateDecomposition` theorem to discharge all three decomposition
hypotheses when `S` is a split torus. It proves

```text
support (imageAction b c d i j hi hj)
  ⊆ Set.image2 (+) (CoordinateWeights.support c) (CoordinateWeights.support d).
```

Thus one character from each input support suffices, and no zero character is
inserted. `image_support_subset_semigroupSum` applies this result to any two
additive subsemigroups containing the respective input augmentation supports.
The conclusion is the literal `semigroupSum A A'` used by the host task.
All actions, eigenconditions and slice identities retain their all-test or
all-coefficient-algebra quantifiers, at arbitrary universe `u`.

The provenance is the coordinate-tensor argument of Conrad–Gabber–Prasad,
*Pseudo-reductive Groups*, second edition (2015), Lemma 3.3.4, printed
pp.108–109 / PDF pp.134–135. This is a derived application of the published
actual-coordinate and tensor lemmas. It does not identify augmentation support
with intrinsic Lie support, prove a generated-subgroup theorem, or prove the
host `SemigroupCommutatorStatement`. Those remain separate obligations.
