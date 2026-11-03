# Nonzeroness of actual standard rational-point induction

Author: Worker 1277.

`RationalStandardInductionNonzeroStatement.{u,v}`, in
`Langlands.Aubert.General.RationalPointFamily`, is an internal prerequisite
for the actual rational-point rank-one length-two target. It states that
normalized induction of every nonzero smooth complex representation of any
standard Levi is nonzero.

The field and carrier parameters remain independent. The field ranges over
all nonarchimedean local fields, the ambient group over all connected
reductive group schemes, and the maximal split torus and generic cocharacter
are those of the published rational-point family. Indices are arbitrary
finite subsets of the literal simple-root type. Representation carriers
have universe `max (u + 1) v`. The topology is exactly `pointTopology`.
The statement retains ambient local compactness and the nonarchimedean
group instance, the existing `StandardCocharacterStatement` premise, and
closedness of the unipotent subgroup at the selected index.

It requires neither irreducibility, cuspidality nor finite length of the
inducing representation. It assumes no parabolic closedness, projection
continuity, unimodularity, geometric lemma, adjointness or cuspidal-support
result. It asserts no composition-length bound or two-factor conclusion.

The provenance is internal. The anticipated derivation transports the
published continuity of the dynamic Levi projection through the three
standard-cocharacter subgroup identities. The resulting smooth inflated
and half-modulus-twisted inducing action permits the published compact local
section construction, whose arbitrary prescribed value proves nonzeroness.
This statement declaration supplies no proof of that argument.
