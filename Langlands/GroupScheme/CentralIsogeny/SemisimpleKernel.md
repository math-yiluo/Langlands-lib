# Killing central semisimple tangent vectors by a central isogeny

Author: Worker 1487.

This internal deduction combines the exact full-centre tangent quotient with
the actual scheme centralizer criterion and smoothness of semisimple
centralizers. It concerns actual dual-number identity kernels and the full
scheme-theoretic centre, including any infinitesimal structure.

Over any commutative ring, for a homomorphism of affine group schemes whose
linear differential kernel is the tangent submodule of the full centre,
`Lie.targetMap_eq_one_iff_elementCentralizer_eq_top` identifies its killed
base tangent vectors with those having the whole group as their actual
centralizer. The proof rewrites differential-kernel membership and applies
`Lie.elementCentralizer_eq_top_iff_mem_center_lie`. The additive wrapper
identifies zero in the linear tangent space with the identity in its
multiplicatively written dual-number kernel.

Over an arbitrary field, when the source is smooth and connected,
`Lie.targetMap_eq_one_iff_elementCentralizerLie_eq_top` gives the equivalent
condition of full Lie centralizer for each representation-semisimple vector.
It uses the proved semisimple centralizer smoothness and subgroup equality
criterion through `SemisimpleCentrality`. No smoothness or reducedness of the
centre is assumed.

`exists_centralIsogeny_killing_central_semisimple` chooses the already
constructed smooth connected affine quotient in positive exponential
characteristic `p > 1`. It retains both central isogeny and the exact
differential-kernel equality on every commutative coefficient algebra, and
adds the preceding equivalence for every semisimple tangent vector over the
base field. One quotient works for all these vectors at once.
`CentralSemisimpleKernelStatement` is the universal proposition expressing
this result, and `centralSemisimpleKernel` proves it in every universe.

This is a supporting result over the base field. It does not claim a
geometric version of the equivalence, prove a decrease of torus weights,
establish termination of successive quotients, lift target tori, or prove the
parent no-torus theorem.
