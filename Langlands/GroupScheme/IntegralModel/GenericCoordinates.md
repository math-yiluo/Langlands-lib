# Actual generic coordinates of an integral group model

Let `R` be a domain, `K` its specified fraction field, and
`M : IntegralModel R K G` a supplied model of the actual group scheme `G` over
`Spec K`. All rings and schemes use one arbitrary universe `u`. This module
compares the original model's global functions with functions and coefficient
points of its specified generic group.

`genericCoordinate` is the ring homomorphism
`Γ(M.group.X.left, ⊤) →+* Γ(G.X.left, ⊤)`. It first pulls a function back along
the first projection from the actual generic fibre and then pulls it back along
`M.genericIso.inv`. The map retains the supplied generic identification.

Assuming `IsAffine G.X.left`,
`adjoin_range_genericCoordinate_eq_top` proves that the image of these original
functions generates the entire generic coordinate algebra over `K`. Its proof
maps the existing first-projection generation theorem through the coordinate
algebra equivalence induced by the generic isomorphism. Surjectivity identifies
the image of the top subalgebra with the top subalgebra, and the composite
pullback is exactly `genericCoordinate`.

For any commutative `K`-algebra `L` with a compatible `R`-algebra structure,
`genericModelPointEquiv L` is an equivalence from the existing coefficient-point
carrier `G.affinePoints (CommAlgCat.of K L)` to the actual relative points
`RingPoint R M.group.X L`. It composes with `M.genericIso.inv` and then applies
the inverse of the actual pullback point correspondence. This construction
does not require affineness of `G`. The theorem
`genericModelPointEquiv_left` identifies its underlying scheme morphism as
composition with the inverse generic isomorphism and the first projection.

`genericModelPointEquiv_evaluation` states that evaluation of any original-model
function at the resulting relative point equals
`G.affinePointEvaluation` of its generic restriction at the original point.
The proof identifies the affine point equivalence with pullback on global
sections followed by the canonical spectrum global-section comparison, then
uses the projection formula and contravariant composition. The model's
affineness supplies the required affine point equivalence.

These are internal constructions derived from `IntegralModel`, the actual
affine base-change coordinate generation and point correspondences, and
naturality of the canonical affine isomorphism. They assume a model, prove no
arithmetic integrality or comparison of integral subgroups, and do not establish
good-model existence, local maximality, covering, or the global Iwasawa-family
existence statement.
