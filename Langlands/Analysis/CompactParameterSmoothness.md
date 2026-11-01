# Smooth parameter families on a compact space

This internal helper develops the supremum-norm calculus needed for smooth
scalar orbit coefficients. The compact space may be empty and need not be a
manifold. The parameter and value spaces are real normed spaces.

`compactFamilyOperator` curries a continuous compact family of continuous
linear operators into an operator with values in continuous functions. Its
operator norm is bounded by the supremum norm of the family.
`compactFamilyOperatorCLM` makes this currying operation a continuous linear map.

`hasFDerivAt_compactFamily` proves that a family of pointwise derivatives which
is continuous in the supremum norm is the actual Fréchet derivative of the
continuous-function-valued map. Continuity gives uniform small variation of
the derivatives on a parameter ball. The normed mean value inequality on that
ball bounds the scalar remainders at every compact-domain point. Taking the
supremum gives the required little-o estimate. The result does not infer
differentiability from continuity of the original family.

`continuousOn_compactFamily_of_joint` obtains continuity by currying a jointly
continuous function after restriction to a compact set.
`contDiffOn_compactFamily_of_joint_aux` inducts over finite smoothness orders,
using joint derivatives restricted to the parameter directions and the
Fréchet differentiation lemma. The universe-general wrapper uses a continuous
linear ULift equivalence so that iterated operator codomains remain in one
universe. `contDiffOn_infty_compactFamily_of_joint` applies all finite orders
to obtain smoothness on the open parameter domain. Equality with the joint
family is required only on that domain.

These lemmas are internally derived from the imported Mathlib calculus and
compact continuous-function norm. They do not yet prove smoothness of an
archimedean orbit or assert density, admissibility or reproduction.
