# Closed-fibre Weyl images and smooth transporters

This internal construction compares the full normalizer action on the
character lattice of a coordinate split torus. It is a derived use of the
published smooth transporter for diagonalizable groups, flat generalization
over a local ring, and rational closed points over algebraically closed
fields. No external-source translation is claimed.

For a finite index type `I`, a field `k`, and a monic inclusion `i` of the
coordinate torus into `G`, `splitTorus.coordinateWeylAction I i` conjugates the
full character-lattice Weyl action by `characterLatticeEquiv k I`.
`splitTorus.coordinateWeylImage I i` is its actual image subgroup in the
integral linear automorphisms of `I → ℤ`. The coordinate change is injective.
The image has the cardinality of `relativeWeylGroup i`, the actual quotient
of normalizer points by centralizer points, because the character action has
exactly the centralizer kernel. A closed torus in an affine locally finite
type group has finite image, using the published full Weyl-image finiteness
theorem. Coordinate image membership is equivalent to existence of a
normalizing point acting through the inverse exponent automorphism.

Let `R` be a local ring, `G` an affine group over `Spec R`, and `i` a map from
the coordinate split torus. Assume the structural morphism of `G` is smooth.
`LocalSplitCorootTransport.IsRealizedAt.of_closedField` says that an integral
torus automorphism realized by a normalizer point over a field `k` mapping
to the closed point of `Spec R` is realized over every algebraically closed
field `l` over `R`.

The proof forms the actual relative transporter between the torus map
precomposed with the inverse exponent automorphism and the original map,
after identifying the split torus with a diagonalizable group. The given
point factors through this transporter, which is smooth over `R`. The
published flat closed-point generalization theorem makes its pullback to
`l` nonempty. Smoothness gives local finite type. A rational closed point
of that pullback supplies an `l`-point of the transporter and hence the
required normalizing point.

For monic torus maps on both field fibres,
`coordinateWeylImage_le_of_closedField` expresses this result as inclusion
of the full coordinate Weyl image on `k` in that on `l`.
`natCard_relativeWeylGroup_le_of_closedField` additionally assumes the torus
map on `l` is closed. Finiteness on `l`, subgroup inclusion, and the
image-quotient cardinality identity then give the corresponding inequality
of actual normalizer modulo centralizer orders.

All constructions are uniform in the universe. Neither connectedness nor
reductivity of `G` is assumed. These results establish an image inclusion
and an order bound, retaining the closed-point, algebraic-closure and
closed-torus hypotheses just stated. They do not identify the two Weyl
images, prove a family connectedness theorem, or prove the host reductive
monomorphism closed-immersion statement.
