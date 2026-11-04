# Positive forms from ambient unimodularity

This derived unit concerns an arbitrary locally compact Hausdorff topological
group and an independent complex representation carrier. It uses the published
normal-subgroup Haar-modulus formula and the published coefficient-integral
positive form. No new literature assertion is used.

`Haar.centralQuotient_isMulRightInvariant` derives right invariance of every
regular Borel Haar measure on the actual quotient by the full abstract center
from triviality of the ambient modular character. The proof uses conjugation by
each specified ambient element. Its restriction to the center is the identity;
the multiplicativity formula for automorphism Haar moduli across a closed normal
subgroup therefore gives modulus one for the induced inner automorphism of the
quotient. Left invariance then identifies this conjugation pushforward with a
right translation pushforward. Second countability is not assumed.

`UnitaryCentralCharacter.unimodularCoefficientProductForm` retains a supplied
unitary full central character, smoothness and irreducibility of the original
action, a specified nonzero algebraic functional, and square integrability of all
its coefficient norms for a specified regular Haar measure on the central
quotient. It derives right invariance and applies the published
`coefficientProductForm`. The result is an invariant positive definite form on
the original representation carrier.

This unit does not prove ambient unimodularity, construct a central character,
or establish square integrability. It supplies a supporting construction for the
strict-exponent branch of the rational rank-one self-association argument; the
exact self-association proposition remains separate.
