# Cuspidal eigenvalue of the general unadjusted Aubert operator

Author: Worker 165, task `e3d69272-2599-4a08-a934-cb11f2493e30`.

`Langlands.Aubert.General.CuspidalEigenvalueStatement` is the separate Prop
target for Aubert 1995, Theorem 1.7(4), printed p.2181 / PDF p.3:
for an actual irreducible cuspidal smooth representation `A`,
`D_G [A] = (-1)^|S| [A]`. This file proves no instance of that assertion.

Immediately before Notation 1.6 on that page, Aubert calls an element of
`Irr(G)` cuspidal when its normalized Jacquet module vanishes for every
proper subset of the simple-root set. `IsStandardCuspidal P M U h hU A`
extends this vanishing condition to objects of the full smooth category.
It means `CategoryTheory.Limits.IsZero ((jacquetFunctor (h I) (hU I)).obj A)`
for every `I ≠ Finset.univ`. The quantified object is the actual normalized
Jacquet module, including its normalizing twist. The eigenvalue target keeps
`A.IsIrreducible` as a separate, explicit hypothesis.

There is no additional admissibility hypothesis in this source convention.
The existing GL predicate `CuspidalSupport.IsLeviCuspidal`, following its BZ
convention, separately includes admissibility. A comparison with that predicate
requires an actual GL specialization and the relevant admissibility theorem;
this helper does not silently replace it. On arbitrary smooth objects,
`IsStandardCuspidal` here names just the stated standard Jacquet vanishing.

The inputs are an actual locally compact nonarchimedean topological group,
a finite index type, actual subgroup families `P`, `M`, `U`, their
semidirect decompositions `h`, closedness `hU`, and the named
`ParabolicFiniteLength` prerequisites `hfl`. The operator is exactly Worker
23's [`alternatingOperator`](AlternatingOperator.md), the unadjusted sum
`∑_I (-1)^|I| i_I r_I`, acting on the exact Grothendieck group of actual
finite-length smooth complex representations at carrier universe
`max uG uV`. Its class formula is already supplied upstream.

The class `[A]` uses the published
`SmoothRep.hasFiniteLength_of_isIrreducible hA`, which derives finite
group-algebra length from simplicity. It requires no admissibility or
finite-dimensional carrier hypothesis. The exponent is `Fintype.card ι`,
the cardinality of the full simple-root index set, and can be zero.

This target is generic in the actual subgroup data. The standard rational-point
realization, including the full subset's identity induction/Jacquet term,
remains required for a connected reductive instance. So do the named
representation-theoretic prerequisites and the eigenvalue proof. No arbitrary
family is asserted to satisfy the target. No split, quasisplit,
characteristic-zero or positive-rank restriction is added.

Source: registered original `aubert-1995-duality`, SHA256
`57af9c46769f6edd8e142ddaf465e89acfa2f2147db222d26879a28a06df9693`,
the cuspidality definition before Notation 1.6, Definition 1.5 and Theorem
1.7(4), printed p.2181 / PDF p.3. The helper's extension of the source
condition to all smooth objects is internal notation. The unresolved
Proposition 3.2 is not used.
