# General Aubert operator and standard-Levi induction

Author: Worker 165, task `e3d69272-2599-4a08-a934-cb11f2493e30`.

`Langlands.Aubert.General.InductionCompatibilityStatement` is the separate
Prop target for the first equation of Aubert 1995, Theorem 1.7(2), printed
p.2181 / PDF p.3:
`D_G ∘ i_J = i_J ∘ D_(M_J)` for every standard subset `J`.
There is no extra rank sign in this equation. This file proves no instance.

All maps are the actual integer-linear maps of Worker 23's
[`AlternatingOperator`](AlternatingOperator.md), on exact Grothendieck groups
of finite-length smooth complex representations, with carriers in
`Type (max uG uV)`. `inductionK0` is the map of the actual normalized
induction functor and has its actual-representation class formula there.
The operator is the unadjusted sum `∑_I (-1)^|I| i_I r_I`.

The ambient group is locally compact and nonarchimedean. The index type
is finite and can be empty. The actual families `P`, `M`, `U` come with
semidirect decompositions `h`, closedness `hU`, and the named prerequisite
`hfl` of finite-length preservation and exactness on finite-length short
exact sequences of both normalized functors.

The additional inputs are visible for every `J`: closedness `hM` of the
Levi, the semidirect decompositions `hLevi` inside that subgroup, and the
matching named prerequisites `hLeviFl`. The Levi operator is exactly
`leviAlternatingOperator P M U J (hM J) (hLevi J) hU (hLeviFl J)`.
Its indexing type is the subtype `J`; `leviIndex J I` reads a finite subset
of `J` as one of the ambient index type and preserves its cardinality.
Its actual subgroups inside `M J` are the `subgroupOf` restrictions of the
same ambient families, so its parabolic is `P_I ∩ M_J` and its radical is
`U_I ∩ M_J`. Local compactness of `M J` comes from `hM J`.
The formula for the Levi operator is the signed sum on these actual
restricted functors, rather than an independent formal endomorphism.

This is a generic actual-subgroup target, pending identification with the
standard rational-point parabolics of a connected reductive group. Actual
Levi decompositions and structural identifications, the named
representation-theoretic prerequisites, and the compatibility proof remain
obligations. No hypothesis is a field supplying the desired map equality.
The statement imposes no split, quasisplit, characteristic-zero or
positive-rank restriction.

Source: registered original `aubert-1995-duality`, SHA256
`57af9c46769f6edd8e142ddaf465e89acfa2f2147db222d26879a28a06df9693`,
Definition 1.5 and first equation of Theorem 1.7(2), printed p.2181 /
PDF p.3. The normalized-functor and Levi-in-Levi construction provenance
is recorded in the upstream paired documentation.
