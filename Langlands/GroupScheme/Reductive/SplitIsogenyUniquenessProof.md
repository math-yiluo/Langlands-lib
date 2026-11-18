# Unpinned uniqueness of split reductive isogenies

Workers 689 and 703.

`Langlands.GroupScheme.splitIsogenyUniqueness` proves the unchanged
[`SplitIsogenyUniquenessStatement`](SplitIsogenyUniquenessStatement.md)
in every universe `u`, with no additional hypotheses.

For arbitrary finite-flat-surjective isogenies between the supplied split
connected reductive groups over any field, equality of pullback on every
character of the target maximal torus implies conjugacy by a unique
ground-field point of the specified actual target adjoint torus. The
conclusion is equality of group-scheme morphisms, so it controls every
test scheme. The point need not lift to a rational point of the original
torus. The full scheme-theoretic centre, possibly inseparable isogenies
and nonsmooth kernels, central torus factors and empty root systems
remain covered.

The Lean proof directly composes two published theorems.
[`splitIsogenyRigidityReduction`](SplitIsogenyRigidityReduction.md) proves
`ReductiveIsogenyTorusRigidityStatement.{u} →
SplitIsogenyUniquenessStatement.{u}`.
[`reductiveIsogenyTorusRigidity`](IsogenyTorusRigidityProof.md) proves its
premise unconditionally in the same universe. Applying the first theorem
to the second therefore discharges the sole premise of the reduction.

The reduction uses separation by the full character lattice to identify
the actual torus restrictions. General rigidity then supplies local
target-torus conjugators with central differences after every refinement.
These descend to a point of the supplied actual adjoint torus. Faithfulness
of its inner action after the isogeny gives uniqueness. The imported
modules explain these implemented arguments.

This is a derived proof using the published Library results. The target's
paired Markdown records its relation to Milne, *Algebraic Groups* (2017),
Propositions 23.5 and 23.7. This module introduces only the final theorem;
the target and its imports are unchanged.
