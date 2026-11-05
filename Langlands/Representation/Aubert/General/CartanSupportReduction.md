# Compact support from bounded Cartan parameters in a valuation kernel

This internal reduction isolates the final finite-support argument needed for the
actual norm-kernel implication in Renard VI.2.1. It is an elementary construction
and proof, not a translation of a separate assertion from the literature.

`JointCartanDetection pair val` means that all integer root coordinates together
with the ambient valuation distinguish the Cartan parameter. The root index may
be empty. Under this hypothesis, `finite_bounded_fiber` places the joint image
in a finite integer box times a singleton, then pulls it back under an injective
map. No finite-generation or lattice-basis hypothesis is needed.

`hasCompactSupport_of_bounded_cartan_parameters` concerns an arbitrary function
on the closed kernel of a group homomorphism `q`. It assumes a compact subgroup
`K` contained in that kernel, a finite residual set, and a Cartan expression for
each nonzero value with integer root coordinates in one fixed bounded box.
Applying `q` to this expression forces the Cartan parameter into the valuation
fiber `(q f)⁻¹` determined by the residual factor `f`. The finite-fiber lemma
makes the union of all possible middle factors finite. The function's support
then lies in the compact product `K D K`, pulled back to the closed subgroup.
Mathlib's compact-support lemma includes the closure of the nonzero locus.

This reduction does not prove joint detection or obtain the coefficient bounds
from cuspidality. In the actual application `q` is the ambient rational-character
valuation and `e` is the uniformizer section followed by the split-torus inclusion.
Finiteness modulo the common root annihilator alone does not discharge the joint
detection hypothesis; central directions must also be detected. In particular,
the empty-root case still requires injectivity of the valuation on parameters.
