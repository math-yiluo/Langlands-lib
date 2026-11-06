# Pinned automorphism rigidity: conditional geometric reduction

Implementation: Worker 1368. Workers 1416 and 1467 supplied the task's
factor-pair, weight-coordinate and root-induction plan; Worker 1467 supplied
the actual root weight-coordinate helper.

This is an internal derivation from the actual pinning, cyclic root and
weight-coordinate constructions, scalar-linear map rigidity, opposite-factor
pair uniqueness, finite Weyl-image reflection comparison, base induction and
closed torus-and-root generation. It proves the exact published
`PinnedAutomorphismRigidityStatement.{u}` from the explicitly defined
`PinnedAutomorphismRigidityPrerequisites.{u}`. It does not prove that target
unconditionally.

The prerequisites are precisely the published maximal-torus self-centralization
statement and existence of actual normalizing opposite factor pairs for every
actual pinning over every field. This second premise is restricted to supplied
split pinnings; it does not assume a general relative-root classification.
Both premises remain proof obligations.

The simple-root step is unconditional. Every vector in the simple Lie weight
line is a scalar multiple of the pinning's chosen vector, by its actual linear
trivialization. Thus fixing the chosen vector under the actual differential
fixes that whole Lie line. Reducedness of the supplied actual root datum
excludes all higher positive root multiples. Splitness of the torus makes its
character lattice torsion-free; the calculation takes place integrally, with
no restriction on the field characteristic. The actual root tangent image is
its positive cyclic weight span; since all higher weights vanish, this image
lies in the original Lie line.

The actual root functor has weight-vector coordinates under that same
no-higher-roots condition. The torus-fixing ambient automorphism restricts to
an actual automorphism of any root representative and commutes with its full
torus action. Uniqueness of the weight scalar structure forces scalar
linearity. The differential is identity on its tangent image, so the vector
endomorphism rigidity theorem proves that the whole root functor is fixed on
every test scheme. This establishes the target's required simple-root
fixedness directly from its differential hypothesis, without assuming fixedness
of root subgroup points or root vectors outside the simple ones.

The previously implemented pinned-root reduction uses actual factor pairs
and their uniqueness to construct fixed reflection normalizers. Finite full
Weyl image identifies their integral reflection functionals with the supplied
root datum. Base induction propagates full subgroup fixedness from the simple
roots to every root. Finally, the subgroup fixed by the automorphism is closed
because it is a scheme equalizer. Self-centralization and closed torus-and-root
generation make it the whole group, so the original automorphism is the
identity. The argument does not assume the fixed subgroup is smooth.

All group schemes, differentials, torus maps and root subgroups are the actual
Library objects. The original statement and its imports are unchanged. All
universes, fields, characteristics and groups with central tori are retained,
including an empty root system. No rank-one existence theorem or torus
self-centralization proof is supplied by this conditional contribution.
