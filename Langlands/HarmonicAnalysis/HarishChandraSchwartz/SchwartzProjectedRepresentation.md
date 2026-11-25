# Right translations on the projected left-invariant Schwartz space

This auxiliary construction implements the function representation used for
the reverse inclusion in Waldspurger (2003), Theorem VIII.4.2, printed
pp.330–331 (PDF pp.96–97). It uses the published Schwartz space and literal
central projection and leaves convergence and finite compact level spans
as explicit inputs.

`schwartzLeftLevel` and `schwartzBiLevel` intersect a Schwartz subspace with
the prescribed left-invariant or bi-invariant function conditions.
`projectedLeftSubrepresentation` is the actual right action on the span of
the raw central image of the left level. Translation stability of the
original subspace and central equivariance prove stability of this span.
Under convergence it equals the raw image. A vector therefore has a
Schwartz preimage and inherits an open right stabilizer from its preimage's
compact open bi-invariance level. Every vector is left invariant under the
prescribed subgroup. When the central measure is right invariant, right
translation by a central element acts by the specified character.

For the admissibility proof, fix a compact open left level H and any open
subgroup J. An H-left-invariant, J-right-fixed vector is bi-invariant under
H ∩ J. This intersection is compact and open. Finite compact averaging
of a cuspidal preimage gives a preimage at that intersection, so the fixed
vector injects linearly into its projected level span. Finite dimension
of these level spans gives finite dimension of all fixed-vector spaces.
Together with smoothness, this proves admissibility.

The construction makes no quotient measure choice and introduces no
normalization of a Haar measure. It supplies the actual representation
and the admissibility deduction, not an invariant positive quotient-L²
form, square integrability of its coefficients, or either of the closed
targets `RationalCuspidalDiscreteCoefficientStatement` and
`RationalCuspidalFixedCoefficientLiftingStatement` (module
`RationalCuspidalCentralStatements`). Those analytic arguments are not made in this module.
