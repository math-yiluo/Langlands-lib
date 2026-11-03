# The actual norm-one Weil restriction

This module constructs the norm-one subgroup of the finite-free
Weil-restricted multiplicative group as an actual group-scheme kernel. It
identifies its points on every test scheme, constructs its splitting from a
product decomposition of the scalar-extended algebra, and specializes this to
finite separable field extensions.

All public declarations below are in `Langlands.GroupScheme.WeilGm`.

## The actual kernel and its point model

Let `A` be a commutative ring and `B` a commutative `A`-algebra that is finite
and free as an `A`-module. These are the hypotheses of the published determinant
norm used here. The generic construction does not impose separability,
smoothness or reducedness.

- `normOne A B` is `kernel (norm A B)` in `Grp (Over (Spec A))`. The kernel is
  the published pullback of the norm morphism along the target unit.
- `normOneCommGroupScheme A B` equips that same actual kernel with its inherited
  commutativity. `normOneι` and `normOneιHom` are its canonical inclusion, in the
  group-scheme and commutative group-scheme categories respectively.
- `normOnePointsEquiv A B T` identifies its group of `T`-points with the kernel
  of `tensorNormUnits A B R`, where `R` is the algebra of global sections of `T`
  over `A`. The coefficient-last tensor convention is `(B ⊗[A] R)ˣ`.
  `normOnePointsEquiv_val` identifies the underlying tensor unit with the unit
  of the included Weil-restriction point.
- `normOneUnitsRestrict` is induced by the tensor extension of the restriction
  on global sections. The determinant norm's published naturality proves that
  it preserves the norm-one subgroup. `normOnePointsEquiv_naturality` proves
  compatibility for every morphism of test schemes.
- `normOneιHom_comp_normHom` proves that inclusion followed by norm is zero in
  the additive notation for commutative group-scheme homomorphisms. As a group
  homomorphism this is the constant unit map.

The test schemes in these assertions are arbitrary schemes over the base,
including nonaffine and nonreduced schemes. The construction uses the actual
scheme kernel; it does not replace it by a subgroup of field-valued points or
assume that general kernels are smooth.

## Product coordinates and actual splitting

For a finite index type `I` and a commutative group `M`, `coordinateProduct I M`
is the homomorphism multiplying all coordinates, and `productOne I M` is its
kernel. Given a chosen coordinate `i₀`, `productOneDropEquiv I M i₀` deletes that
coordinate. Its inverse inserts the inverse of the product of the other
coordinates. The proof uses the decomposition of a finite product into its
chosen factor and the product on the complementary subtype. The equivalence
also covers a singleton index type, whose complement is empty.

Now let `A'` be a commutative `A`-algebra and suppose an actual algebra
equivalence is supplied:

`e : A' ⊗[A] B ≃ₐ[A'] (I → A')`.

The generic section uses `Fintype I` and `DecidableEq I`. There is no field
hypothesis on `A` or `A'`. A chosen `i₀ : I` supplies the required nonempty
index when constructing the split-torus isomorphism.

`normOneDecompositionPointsEquiv` identifies points of the actual base change
of `normOne A B` with product-one families of global units. It composes the
published kernel/base-change comparison, the actual kernel point equivalence,
and the published Weil-restriction decomposition. The norm's product-coordinate
formula verifies that these equivalences preserve the two kernels. The target
multiplicative-group comparison is accounted for by
`Gm.baseChangeUnitsEquiv`.

`normOneDecompositionPointsEquiv_val` proves that these coordinates are exactly
`decompositionPointsEquiv` of the image under the base-changed kernel inclusion.
It uses the compatibility of `kernelBaseChangeIso` with inclusion. Deleting
`i₀` gives `normOneSplitPointsEquiv`; its naturality follows from this value
formula and the published naturality of decomposition coordinates.

`normOneDecompositionIso A A' B I e i₀` is the resulting actual isomorphism

`(normOne A B) ×[Spec A] Spec A' ≅ splitTorus (Spec A') {i : I // i ≠ i₀}`.

It is constructed by the published Yoneda point-model isomorphism, with the
proved natural multiplicative equivalences on all test schemes.
`normOneDecompositionIso_hom_points` identifies every retained coordinate with
the corresponding coordinate of the included Weil-restriction point.
`normOneDecompositionCommIso` is the same actual isomorphism in the commutative
category, with the homomorphisms written additively.

## Finite-separable field specialization

Let `K/k` be a finite separable field extension. Let `Ω` be any field extension
of `k` in which the image of the minimal polynomial of every element of `K`
splits. No normality or Galois assumption on either extension is imposed.

`normOneSeparableEmbeddingIso k K Ω hsplit τ₀` specializes the generic
construction to the published canonical algebra decomposition indexed by
`K →ₐ[k] Ω`, deleting any chosen embedding `τ₀`. Thus its target split torus is
indexed by `{τ : K →ₐ[k] Ω // τ ≠ τ₀}`. The corresponding commutative isomorphism
is `normOneSeparableEmbeddingCommIso`.

`normOneSeparableEmbedding_card` proves that the natural cardinality of this
index type is `Module.finrank k K - 1`, using the published embedding count and
the cardinality of the complement of a singleton. This counts the factors of
the displayed actual splitting.

`separableEmbedding_nonempty` obtains an embedding from that count and the
positive degree of a field extension. Finally,
`normOne_isTorus_of_finite_separable` takes `Ω = SeparableClosure k`, uses the
published splitting of separable minimal polynomials there, chooses an
embedding, and exhibits this split-torus isomorphism as the witness for the
Library's `IsTorus` proposition. In degree one the displayed split torus has
zero factors.

## Provenance and scope

This is an internal construction from the published `WeilRestrictionNormSplit`,
`WeilRestrictionSeparable`, actual kernel/base-change, and split-torus point-model
APIs. The new proofs are the intrinsic laws and comparisons of these
constructions; no external structural assertion is assumed.

This module constructs the actual norm-one torus and its splitting. It does not
construct its character or cocharacter exact sequences or identify their
Galois actions, assert descent of points, or construct the general finite-Galois
point norm of an arbitrary commutative affine group scheme. Those are separate
extensions. The generic finite-free kernel remains defined without any claim
that every such kernel is a torus.
