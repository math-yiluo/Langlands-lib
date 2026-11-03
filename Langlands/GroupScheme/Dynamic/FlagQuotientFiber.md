# Actual fibers of exact coset quotients

This internal construction starts with an actual group scheme `G` over any
scheme `S`, an actual relative scheme `Q`, a morphism `q : G.X ⟶ Q`, and a
section `p : S ⟶ Q` over the base. The fiber is the actual scheme pullback
of `q.left` and `p.left`, with its second projection as structure morphism
over `S`. The inclusion, factorization, extensionality and lift lemmas express
this actual pullback universal property. Flatness, surjectivity and
quasi-compactness of `q.left` pass to its structure morphism by base change.

For a group-scheme homomorphism `i : P ⟶ G`, assume the exact fiber criterion
on every relative test scheme: quotient images of `g` and `h` agree precisely
when `g⁻¹ * h` factors through `i`. The action on the fiber is
`a • g = g * (i(a))⁻¹`. The inverse is essential for this to be a left action.
The exact fiber criterion proves this product remains in the same fiber.
The action's naturality, unit and multiplication laws follow from pullback
extensionality and the ordinary group laws on each test. Evaluating on the
universal product test gives an actual action morphism.
`schemeActionOfPointLaws` packages these laws as Mathlib's standard `ModObj`.

When the subgroup inclusion is a monomorphism, the exact fiber criterion
gives simple transitivity on every relative test scheme. For two fiber
points with group components `x` and `y`, choose the unique subgroup point
mapping to `y⁻¹ * x`. It sends `x` to `y` under the action above. Group
cancellation determines its image uniquely, and the monomorphism determines
the subgroup point uniquely. Mathlib's all-test characterization of
`ModObj.leftSMul` therefore proves that the actual shear
`P × X → X × X`, `(a,x) ↦ (a • x,x)`, is an isomorphism.

Over a finite field, `rational_lifts_of_finite_torsor` applies the separate
`FiniteFieldTorsorPointStatement` to this actual fiber. Its three cover
conditions follow by base change from `q`; the action and shear come from
the constructions just described. A rational point of the fiber, composed
with its inclusion into `G`, lifts the original quotient point. The proof
uses `rationalPointEquiv` to preserve the published `RingPoint` convention.
The subgroup's smoothness, affineness and connectedness and the finite-field
torsor point proposition are explicit inputs. This unit proves no
unconditional finite-field lifting or quotient-existence theorem.

The provenance is internal, from actual pullbacks, the all-test fiber
equivalence and the existing categorical group and action APIs.
