# The linear unit-stalk comparison

This internal module derives the local-ring linear form of elementary stalk
comparisons from Mathlib's colimits and stalk scalar actions.

`unitStalkLinearEquiv` identifies the actual stalk of the unit module sheaf
with the actual scheme local ring. Its underlying additive isomorphism is the
comparison of a filtered colimit with its image under the forgetful functor
from commutative rings through rings to abelian groups. The germ comparison follows from
the colimit comparison formula. Linearity follows by representing a scalar
and a module element over a common neighborhood and using
`PresheafOfModules.germ_smul`. `unitStalkLinearEquiv_germ` records the
resulting equality on actual germs.
