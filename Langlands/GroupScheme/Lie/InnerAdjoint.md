# Differentials of actual inner automorphisms

`Lie.innerDifferentialEquiv` is the linear equivalence on the actual
dual-number identity kernel induced by the inner automorphism of a supplied
base section. It is the published `Lie.targetEquiv` of that actual group
isomorphism, so its inverse is the differential of the inverse isomorphism.
It is defined over every coefficient algebra.

The differential of the inner automorphism attached to an actual group section
over the base is the published adjoint action of that section, after extending
it to any coefficient algebra. The proof compares the actual dual-number
points. The published inner-automorphism formula gives conjugation by the
pulled-back section, and naturality of constant points identifies that section
with the constant dual-number lift used by the adjoint action.

For an actual relative exponent weight vector over an arbitrary commutative
ring, a torus base section therefore acts on the vector by its exponent value.
This follows by testing the defining all-algebra weight equation at the base
ring and using the identity coefficient map. Consequently, when the
differential of a supplied group homomorphism sends a vector to a unit multiple
of that weight vector, composing with an actual target torus inner
automorphism removes the multiple if its exponent value is the inverse unit.
Linearity and the unit inverse equation prove the final claim.

These are internal deductions from `InnerAutomorphism`, the actual adjoint and
kernel-map constructions, `Torus/RelativeAdjointWeights`, and the published
composition law and isomorphism equivalence for differentials. The torus section and its exponent value
are explicit inputs. No existence claim for such a section is made.
