# Point Weyl orders over a split local base

This internal supporting construction combines the Library point-quotient transport and local split Weyl-order results. The point quotient is always the group of actual all-test normalizer points modulo its subgroup of all-test centralizer points.

For a closed coordinate torus map over any commutative ring `R`, `splitTorus.fibreRelativeWeylGroupEquiv` identifies the rational Weyl quotient of its actual coordinate field fibre with the original point Weyl quotient evaluated on `Spec k ⟶ Spec R`, for every supplied `R`-algebra field `k`. The proof passes between rational points and the all-test functors at the field base, removes the canonical split-torus source isomorphism, and uses arbitrary base-change transport. Closedness supplies monomorphisms for both the pulled-back map and its coordinate-source form. It imposes no reductivity or maximality.

For a reductive affine group over a local ring, a closed coordinate torus map that is fibrewise maximal therefore has the same point-quotient order on every such field-valued test scheme. The theorem `natCard_pointWeylGroup_eq_localSplitWeylOrder` transports the cardinality through the preceding equivalence and applies the common-order theorem from `LocalSplitWeylOrder`. It uses the original supplied algebra structure on `k`; the common natural number depends on the local group and torus map and is independent of the field algebra.

These are point-quotient comparisons. They do not construct a quotient scheme or assert that its points agree with the point quotient.
