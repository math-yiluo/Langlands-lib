# Evaluation of compatible parabolic root cones

This internal construction evaluates a real character of the specified split component
on the integral defining cocharacter `splitComponentCocharacter` of a compatible
`ParabolicRootPresentation`. The result is the real linear map
`splitComponentEvaluation`. The field has arbitrary universe and characteristic;
no root-system realization or linear-independence premise is used.

The tensor formula is the scalar extension of the published lattice pairing.
Every restricted simple root evaluates positively because its integral restricted
character belongs to `intrinsicPositiveRoots`, as proved by
`restrict_mem_intrinsicPositiveRoots`. For a locally finite type ambient group,
the restricted-root set is finite. Applying the linear map term by term to the
finite sums defining `nonnegCone` gives a nonnegative value. Applying it to the
strictly positive coefficients defining `positiveCone` gives a strictly positive
value when that root set is nonempty.

It follows that zero belongs to the strictly positive cone if and only if the
restricted-root set is empty, equivalently if every ambient simple root is in
the presentation index. In the empty case the cone is the singleton consisting
of zero. The distinction matters: the strictly positive cone uses every
restricted simple root, including when there are no such roots.

These are derived facts about the published constructions, motivated by the
forward implication of Renard 2026, VII.2.4, Lemma (printed p.230 / PDF p.236).
They do not assert that a proper parabolic has nonempty restricted roots, do not
construct presentations for arbitrary triples, and do not prove Casselman's
criterion or the square-integrability equivalence. Those structural and
representation-theoretic obligations remain separate.
