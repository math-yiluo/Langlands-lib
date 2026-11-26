# A uniform pro-\(p\) kernel on compactly supported cohomology

## Source

Michael Harris, *Galois properties of cohomological automorphic forms
on GL(n)*, J. Math. Kyoto Univ. 39 (1999), §2, Facts 1 bis and 2,
printed p. 303, exact sequence (2.1), p. 304, and the paragraph after
(2.3), p. 305. These are
PDF pp. 5–7 of the retained copy, registered as
`harris-1999-cohomological-automorphic-forms-525a222c4489ee9d`,
SHA-256 `525a222c4489ee9d3fe86a52c6c17ffb30fcc7c31f24c16a64669e9615085b26`.
[Retained article](../../../notes/henniart/sources.md#ha99)

Harris uses the finiteness and boundedness of compactly supported
cohomology on his test space to take one open normal pro-\(p\)
subgroup of its compact stabilizer that acts trivially on
cohomology for every degree and every \(\ell\)-power coefficient
level. He uses \(p\ne\ell\) for exactness of this subgroup's
invariants on the torsion modules. The compact-support dimension
bound over the geometric base is the absolute case of Berkovich,
*Étale cohomology for non-Archimedean analytic spaces* (1993),
Corollary 5.3.8, pp. 104–105, PDF pp. 101–102, registered as
`berkovich-1993-etale-cohomology`, SHA-256
`06b42aca1c8f237e607d2cf1f15a41fdc9718324a4dc9fd5bce66574254bb91c`.
The proposition isolates the group-action step for an
\(\ell\)-divisible system on an étale site.

## Lean proposition

`Langlands.Cohomology.DivisibleSystem.Analytic.AnalyticEtaleCompactUniformProPKernelStatement`
uses `EtaleDivisibleSystem` and the actual smooth compactly
supported cohomology `etaleGSheafCompactCohomology`. The analytic
space `X` and action `ρ` are over a fixed complete ultrametric
field `K`. The group `G` is compact Hausdorff and topological,
with `Small G` in the module universe. The construction uses the
admissible refinements of the distinguished étale lift system and
compact supports on the `L`-valued points satisfying the étale
point axioms, for the normed extension `L/K`.

The coefficient ring `R` is commutative, \(\ell\) is prime, and
`G` has some open normal pro-\(p\) subgroup for \(p\ne\ell\).
Primality of \(p\) is part of `IsProPSubgroup`. The ring hypothesis
`IsUnit (p : R)` makes exactness of pro-\(p\) invariants applicable
to smooth `R`-modules. For example, \(R=\mathbb Z_\ell\) gives
Harris's quotients \(R/\ell^m R\) at coefficient level \(m\).

Given a bound \(D\) on nonzero cohomology for `T.obj 1` and
finiteness in degrees at most \(D\) at that level, the proposition
asserts finiteness and the same bound at every level. It also
asserts that some open normal pro-\(p\) subgroup acts as the
identity on the actual smooth cohomology representations
simultaneously at every level and degree.
`etaleCompactCohomologyAtLevel` evaluates the cohomology functor
at the specified coefficient level and uses `SmoothRep.toRep`
to read the underlying representation and its action.

The short exact sequences \(0\to T_m\to T_{m+1}\to T_1\to 0\)
are the successive instances of (2.1). In the associated long
exact cohomology sequence, the middle group in degree \(q\) is
an extension of a subobject of the level-\(1\) group by a quotient
of the level-\(m\) group in degree \(q\). This gives finiteness
and the bound by induction. Smoothness and finiteness let one
intersect the kernels on the finitely many level-\(1\) groups
with the given open normal pro-\(p\) subgroup. The intersection
is a closed subgroup of that pro-\(p\) group. Exactness of its
invariants then propagates triviality from level \(1\) to
every level via the same extensions. Level \(0\) of the system
is zero.
