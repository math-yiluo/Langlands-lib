# The actual degree-two sum map for an abelian variety

This internal specialization lives in
`Langlands.AbelianScheme.CanonicalDegreeTwoSum`. Let `K` be an arbitrary field
and `A` an abelian scheme over `Spec K`. All cohomology groups below are the
Library's actual right-derived unit-module cohomology over `K`.

## Cover and map

`productCover A` is the simple product family
\(p_1^{-1}U_i\cap p_2^{-1}U_j\) formed from the chosen finite affine cover
`Langlands.AbelianScheme.cover A`. Here `p₁` and `p₂` are the actual categorical
projections `A.X ⨯ A.X → A.X` over `Spec K`. `productCover_top` proves that
this family covers, by the covering property of each factor.
`productCover_affine` follows from the actual pullback square and affineness
of the two factor opens. This simple family differs from the multiplication
adapted family `Langlands.AbelianScheme.productCover`, which also intersects
the inverse image of a third cover member under multiplication.

`sumMap A` specializes `AllSeq.degreeTwoSum` to these projections and this
simple product cover:
\[
H^2(A)\times\bigl(H^1(A)\otimes_K H^1(A)\bigr)\times H^2(A)
  \longrightarrow H^2(A\times_K A),
\qquad (x,t,y)\longmapsto p_1^*x+\operatorname{mixedTensor}(t)+p_2^*y.
\]
The Lean domain is right associated. Its mixed term is the actual cup on the
simple product cover, with the first projection's degree-one class as the
left factor and the second projection's class as the right factor.

## Injectivity and projection formulas

`sumMap_injective` proves injectivity for every such `A` with no additional
hypotheses. It instantiates `AllSeq.degreeTwoSum_injective_of_points` as follows:

- the categorical product in schemes over `Spec K` gives the actual underlying
  pullback square;
- separatedness of `A` and its product supplies the comparison hypotheses;
- on every open, take the section algebra induced by `secHom` of the structure
  morphism, so all three scalar compatibility equalities are reflexive;
- the chosen affine cover has finite indexing, covers `A`, and has affine
  members; separatedness makes all its nonempty finite intersections affine;
- the simple product cover is finite, covering and affine by the two lemmas
  above;
- the unit morphism of `A` supplies each rational point required by the general
  injectivity theorem. Its source is the categorical unit over `Spec K`,
  definitionally the identity object `Spec K` over itself.

Thus arbitrary-dual shuffle slant detects the mixed tensor, and the unit axes
detect the two remaining degree-two classes, as proved in the general theorem.

`sumMap_left` and `sumMap_right` compute this map on `(x,0,0)` and `(0,0,x)`.
They give exactly `pullStructure A p₁ 2 x` and `pullStructure A p₂ 2 x`.
The actual unit-module pullback used by `AllSeq.degreeTwoSum` is definitionally
the canonical `pullStructure` map used by the host statement.

## Provenance and scope

This is a derived specialization of `AllSeq.degreeTwoSum`, its proved
rational-point injectivity, and the finite-cover and product infrastructure
in `CanonicalH1Primitive`. No new literature theorem is asserted.
The field may have arbitrary characteristic; no finite-dimensionality,
exterior-generation or degree-two primitive-injectivity result is used.

This unit proves the particular sum map injective and computes its two pure
projection terms. Surjectivity, an inverse Kunneth equivalence, identification
of cups from different covers, alternation, creation-contraction identities,
exterior generation and the host comparison are not proved here.
