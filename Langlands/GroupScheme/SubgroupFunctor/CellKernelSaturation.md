# Kernel saturation and inverse images of binary open cells

This internal supporting construction concerns actual binary multiplication
cells over an arbitrary base scheme. It derives its claims from the
scheme-theoretic kernel, group operations on all relative test schemes,
compatible cell multiplication, and factorization through an open immersion.

Let `q : G → H`, `i : U → G`, and `p : P → G` be homomorphisms.
Suppose a morphism `κ : ker(q) → U × P` composes with the actual ordered
multiplication `cellMultiplication i p` to the original kernel inclusion.
The morphism `κ` need not preserve a group law.

`exists_lift_mul_kernel` proves that every product of a point of the cell
with a point of the full kernel lies in the same cell, on every test scheme.
Writing the first point as `u p₀` and the kernel point as `n`, the proof
factors `p₀ n p₀⁻¹` through the full kernel and then through `κ`. If its
cell coordinates are `a b`, the required coordinates are `u a` and `b p₀`.
The group identity `(u a)(b p₀) = (u p₀)n` proves the assertion.
No reducedness, smoothness, or field assumption is used in this step.

Now suppose `f : U → V` and `g : P → R` are scheme-surjective
homomorphisms commuting with `q` and target inclusions `j : V → H`,
`r : R → H`. Assume the source cell is an open immersion.
`exists_lift_iff` proves that a test morphism into `G` factors through
the source cell if and only if its image under `q` factors through
the target cell. The forward direction is compatibility of multiplication.
For the converse, the product map `f × g` is surjective, so its pullback
along the target coordinates gives a surjective cover with source
coordinates. The difference between the lifted product and the original
point lies in the full kernel. The preceding saturation identity gives
a source-cell factorization over the cover. Surjectivity detects
containment of the original topological image in the source open cell;
the universal factorization property of an open immersion then gives
the desired morphism over the original test scheme.

`quotientCellLift` chooses these source coordinates from supplied target
coordinates. `quotientCellLift_comp` identifies their ambient composite
with the original test morphism.

Only scheme surjectivity of the factor maps is needed. The proof makes
no assertion of surjectivity on points over a ground field. It supplies
an inverse-image and saturation step for compatible cells; constructing
the kernel chart and applying the result to dynamic groups and integral
opposite factors remain separate obligations.
