# Smoothness transport for character-kernel centralizers

This derived unit transports actual automorphic actions along isomorphisms
of the acting group. `AutomorphicAction.reparametrize a e` is the existing
restriction of the action along the homomorphism of the supplied
group-scheme isomorphism `e`. Its pointwise action is the original action
after composition with that homomorphism.

`isFixed_restrict_iso` and `fixedSubgroup_restrict_iso` preserve the full
all-test, all-refinement fixed functor. In one direction every acting point
is pulled back along the inverse isomorphism and then pushed forward along
the isomorphism; the two morphisms cancel. The other direction applies
original fixedness to the image of the acting point. The resulting equality
is an equality of subgroup functors, with no assumption of reducedness or
smoothness of the actor.

`Diagonalizable.fixedSubgroup_smooth_of_actingIso` retains the explicit
premise `Diagonalizable.FixedSubgroupSmoothStatement`. It reparametrizes an
action by an isomorphism from its actor to the actual diagonalizable group
of a finitely generated abelian character group. The fixed-functor equality
lets the supplied closed representative satisfy the hypotheses of that
general smoothness statement. The ambient group is smooth and affine over
an arbitrary field. The character group may have torsion.

`RelativeRoot.kernelCentralizer_smooth_of_diagonalizableIso` specializes
this transport to the actual character kernel acting by restriction of
conjugation. Both the general smoothness statement and an actual isomorphism
of the kernel to a finite-type diagonalizable group remain explicit
premises. The result concerns any supplied closed representative of the
existing kernel-centralizer functor. No split-torus, nonzero-character or
primitivity assumption is needed for this conditional specialization.

These are internal consequences of the published action restriction,
fixed-subgroup, character-kernel and diagonalizable-group constructions and
the published smoothness statement interface. This file proves neither the
general smoothness statement nor existence of a closed representative or
of a diagonalizable model for the kernel.
