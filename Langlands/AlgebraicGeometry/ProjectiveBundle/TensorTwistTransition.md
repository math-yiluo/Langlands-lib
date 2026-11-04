# Degree-one transitions after tensoring genuine frames by a line

For a locally free module sheaf `M` of rank `n + 1` and a line module
sheaf `N` on a scheme `S`, this module compares the actual degree-one
transitions of the joint tensor and source frame atlases. Their open
covers agree. `dualLineTransitionUnit` is the reversed comparison unit
of the chosen line frames on an inclusion `U → V`, transported from
sections on `U` to global sections of `U.toScheme`.
`dualLineProjectiveUnit` is its image under the actual structure-map
homomorphism to global sections of the relative projective chart.

`tensor_transition` expresses the tensor dual-coordinate change as the
source change followed by multiplication by this reversed unit.
`tensor_chartTwistIso` compares the actual pullback isomorphisms of the
standard degree-one bundles: transport along the proved equality of
projective restriction maps, apply the source twist comparison, and
then apply the published module automorphism `unitAut` for
`dualLineProjectiveUnit`. The scalar is retained on the degree-one
bundle even though it acts trivially on the projective scheme.

The proof first computes the effect of multiplying a coordinate matrix
by a scalar unit on transformed sections. A general criterion
`pullback_comparison_scaled` compares two pullback isomorphisms over
equal scheme maps by their values on a covering family of line-bundle
sections. For arbitrary coordinate cocycles on the same locally
directed open cover, `chartTwistIso_coordinate_scaled` gives the scaled
coordinate formula. `chartTwist_scaled_criterion` allows arbitrary
pullback comparisons with the expected coordinate formulas;
`chartTwistIso_scaled` specializes it to the actual chart comparisons.
The tensor case follows from the published arbitrary-overlap dual-frame
formula and the equality of its scheme transition maps.

This is an internal consequence of the existing frame, coordinate, and
line-bundle constructions in `TensorLineInvariance`, `TwistTransition`,
and `ScalarTwist`. It asserts no additional theorem from the literature.
Global tensor-line gluing and ordinary moduli representability remain
further obligations.
