# The nested Levi face of the fine nonnegative root cone

Worker 17. This internal support retains supplied compatible fine and outer
parabolic root presentations, the original fine-Levi map into the original
outer Levi, its ambient compatibility, and the displayed affine and finite-type
instances. Connected reductivity of the ambient group and all-test containment
of the fine parabolic in the outer one are hypotheses of the cone comparison.

`outerComponentRestriction` is real character restriction along the actual
outer-to-fine split-component factor constructed by the published intermediate
factorization. On a restricted fine root vector it is restriction of the same
original root to the original outer split component.

The factor of the fine torus into the actual outer Levi preserves the original
outer split-component map: its composite equality follows by cancelling the
closed outer-Levi inclusion. Centrality of the specified outer component then
shows that every actual outer-Levi root restricts to zero.

`outerFaceNonnegCone` uses the actual roots of the fine torus in the original
outer Levi, the fine generic cocharacter, selected roots and component factor.
The preceding root comparison identifies its simple roots with the outer zero
face. Its generators therefore form a subset of the fine cone generators and
restrict to zero, giving one implication of `mem_outerFaceNonnegCone_iff`.

For the other implication, expand a fine cone vector over the finite family of
fine simple roots outside the selected set. Evaluate its zero outer restriction
on the outer defining cocharacter. The result is the sum of each nonnegative
coefficient times the corresponding nonnegative transported pairing. Each
summand is zero. A root outside the zero face has nonzero pairing, so its
coefficient is zero. Removing those terms leaves exactly the finite family for
the actual outer-Levi face cone. This argument permits repeated restricted root
vectors, empty faces and nonreduced root systems, and assumes no independence
of simple roots.

The provenance is the preceding actual torus and zero-face constructions,
central split-torus root restriction, finite-family cone enumeration and
nonnegative finite-sum arithmetic. This result establishes a cone slice only.
It does not construct an inner compatible parabolic presentation, identify
cones for arbitrary other presentations, or prove either remaining whole
representation-theoretic target of Renard VII.2.3–VII.2.4.
