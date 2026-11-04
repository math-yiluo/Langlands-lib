# Dimensions of actual smooth homogeneous quotients

This module constructs constant relative-dimension data for a supplied smooth
exact homogeneous quotient and derives its actual Lie-dimension formula. The
field `k : Type u` is arbitrary, with no characteristic restriction.

## Rational sections and smooth dimensions

`Langlands.AlgebraicGeometry.isClosed_singleton_section_point` says that the
underlying point of any section `Spec k → X` of a `k`-scheme is closed. The
proof uses Mathlib's closed-immersion theorem for a section over a subsingleton
base, and identifies the image of that section with the singleton. It needs
neither separatedness nor local finite type of `X`.

`relativeDimension_cast_le_topologicalKrullDim_of_section` assumes such a
section and `SmoothOfRelativeDimension d X.hom`. It proves

```text
(d : WithBot ℕ∞) ≤ topologicalKrullDim X.left.
```

The published `fieldSmoothClosedPointStalkDimension` identifies the stalk
Krull dimension at the section's closed point with `d`. Mathlib identifies
this stalk dimension with the coheight of the corresponding irreducible
closed set. Coheight is bounded by the Krull dimension of that poset, which
is the scheme's topological Krull dimension.

`Lie.dimension_eq_of_smoothOfRelativeDimension` specializes the same stalk
comparison to the identity section of an affine group scheme `G`. Its
conclusion is `Lie.dimension G = d` for any supplied constant smooth relative
dimension `d`. The published `Lie.finrank_kernel_cast_eq_ringKrullDim` gives
the first equality, between the actual dual-number Lie finrank and the
identity stalk dimension. No connectedness is needed for this lemma.

## The dimension data

Let `i : P ⟶ G` be a group-scheme homomorphism and `q : G.X ⟶ Q` a morphism
over `Spec k`. `HomogeneousQuotient.DimensionData i q` stores natural numbers
`fiberDimension = n` and `quotientDimension = d`, together with:

- smooth relative dimension `n` for `P → Spec k`;
- smooth relative dimension `n` for `q`;
- smooth relative dimension `d` for `Q → Spec k`;
- smooth relative dimension `n + d` for `G → Spec k`.

The `dimensionData` construction assumes `G` smooth and connected, the
underlying map of `i` monic, and `q` smooth and surjective. Its remaining
hypothesis is the exact coset relation on every scheme test `T`:

```text
g ≫ q = h ≫ q ↔ g⁻¹ * h ∈ (SubgroupFunctor.range i).carrier T.
```

There is no affineness assumption in the construction. Smoothness descends
from `G → Spec k` along the smooth surjection `q`, and surjectivity transfers
connectedness from `G` to `Q`. The published
`smoothConnectedRelativeDimension` then supplies the constants `n` for `q`
and `d` for `Q → Spec k`.

The actual identity coset `Spec k → Q` defines a scheme fiber of `q`. Smooth
relative dimension is stable under base change, so that fiber has dimension
`n`. The published `subgroupIdentityFiberIso`, using monicity and the exact
all-test coset relation, identifies this fiber with `P` over `Spec k`.
Transport through that isomorphism gives the subgroup's smooth relative
dimension. Composition of the two smooth relative dimensions gives `n + d`
for `G`. Classical choice selects a complete datum from this existence
proof; no canonical choice of natural numbers is claimed.

## The Lie-dimension formula and curve consequence

For affine `G` and `P`, `DimensionData.lie_dimension_eq` applies the preceding
Lie/stalk comparison to its subgroup and ambient fields and proves

```text
Lie.dimension G = Lie.dimension P + D.quotientDimension.
```

`DimensionData.quotientDimension_cast_le` uses the actual identity coset
section and the rational-section bound to compare `D.quotientDimension`
with `topologicalKrullDim Q.left`.

`lie_dimension_le_add_one_of_dimension_le_one` retains the exact-fiber,
smooth-surjective and connected-source hypotheses of `dimensionData`, assumes
both groups affine, and assumes `topologicalKrullDim Q.left ≤ 1`. Choosing
the datum, bounding its quotient dimension by one, and applying the formula
proves

```text
Lie.dimension G ≤ Lie.dimension P + 1.
```

The subgroup need not be connected, and smoothness of `P` follows from the
actual identity fiber rather than being an additional premise.

## Provenance and application boundary

This is an internal derivation from the published exact homogeneous-quotient
fiber construction, smooth-source descent, constant relative dimension for a
smooth map with connected source, closed-point smooth stalk dimension, and
the actual affine-group Lie/stalk comparison. Mathlib supplies closedness of
a section over a one-point base, smooth base change and composition, and the
order-theoretic dimension bound. The quotient-dimension step belongs to the
prescribed-Borel route discussed by Workers 1547 and 317; Worker 1547
implemented the construction and proofs here. No external structural theorem
is asserted.

The module takes the quotient, smooth surjectivity, its exact coset fibers and
the dimension bound as inputs. It constructs none of these application data
and does not prove `RankOnePositiveRootUniquenessStatement`. In particular,
the rank-one Borel quotient dimension bound, fixed-point and torus arguments,
and the comparison with positive roots remain separate proof obligations.
