# Bounded adjoint preimages inside the rational norm kernel

Let `F : Type u` be a nonarchimedean local field with its compatible valuation
and topology. Let `G` be connected reductive and let `q : G ⟶ A` satisfy the
actual full-center quotient predicate `IsAdjointQuotient q`. The proved
definition `isAlgebraicallyBounded_adjoint_preimage_inter_normKernel` states
that, for every algebraically bounded subset `B` of `A(F)`, the set

`(rationalPoints.map q ⁻¹' B) ∩ rationalCommonNormKernel G`

is algebraically bounded in `G(F)`. The explicit affine instances in its
signature are satisfied by these reductivity and adjoint-quotient hypotheses.
The field and schemes retain arbitrary universe `u`.

The auxiliary theorem `isAlgebraicallyBounded_pointPair` treats two affine
schemes locally of finite type over `F`, with affine product. It bounds the
image of the Cartesian product of two bounded sets under the actual product
point pairing. Each set has compact closure in the canonical rational-point
topology. The pairing is continuous by comparison with the chart topology on
scheme points; the local-field Hausdorff instance supplies the required open
units. The image of the product of the two compact closures is compact and
therefore algebraically bounded, and contains the required image.

The auxiliary theorem `mapsTo_rationalCommonNormKernel` applies to any
homomorphism of group schemes over `F`. Every rational character of its target
pulls back to an actual rational character of its source. Naturality of
character evaluation shows that a point in the source common norm kernel maps
into the target common norm kernel.

For the main assertion, the published derived-subgroup representability and
normal-subgroup quotient results construct an actual closed derived inclusion
`d : D ⟶ G` and an affine smooth fppf quotient `p : G ⟶ Q` by its full range
functor. Reductive central-torus surjectivity and the derived-quotient theorem
show that `Q` is a torus. The geometric helper `isFinite_adjoint_cocenter`
proves that the actual paired homomorphism `lift q p : G ⟶ A ⊗ Q` is finite.
Its finite kernel is the full central intersection with the derived subgroup.

The torus norm-kernel compactness theorem makes `rationalCommonNormKernel Q`
compact, hence algebraically bounded. The product-pairing result then bounds
`B × rationalCommonNormKernel Q` as a set of points of `A ⊗ Q`. Pullback along
the finite paired morphism preserves algebraic boundedness. The character
pullback theorem places every point of the displayed set in this finite
preimage, so boundedness follows by monotonicity. The equality between the
paired point and postcomposition with `lift q p` follows from the product
universal property.

This is an internal composition of the stated geometric and analytic Library
results, together with the bundled finite-map helpers. It discharges the
bounded-preimage input of the adjoint reduction without requiring surjectivity
on rational points. The normalizer-image input remains separate; this module
alone does not prove the bounded-open-normalizer theorem.
