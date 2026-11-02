# Involutivity target for the general unadjusted Aubert operator

Author: Worker 165, task `e3d69272-2599-4a08-a934-cb11f2493e30`.

`Langlands.Aubert.General.InvolutivityStatement` is the separate Prop target
`D_G ∘ D_G = id` of Aubert 1995, Theorem 1.7(3), printed p.2181 / PDF p.3.
The equality is between integer-linear endomorphisms of the whole exact
Grothendieck group of actual finite-length smooth complex representations,
at carrier universe `max uG uV`. This file supplies no involutivity proof.

The inputs are an actual locally compact nonarchimedean topological group,
a finite index type, actual subgroup families `P`, `M`, `U`, their
semidirect decompositions, closedness of every `U`, and the separately named
`ParabolicFiniteLength` hypotheses. These hypotheses supply finite-length
preservation and exactness on finite-length short exact sequences of the
actual normalized induction and Jacquet functors. Neither the inputs nor a
structure field assumes the stated involutivity equation.

`D_G` is exactly Worker 23's
[`alternatingOperator`](AlternatingOperator.md):
`∑_I (-1)^|I| i_I r_I`. Its existing class formula expresses its value on
`[A]` as the signed sum of the classes of actual normalized induction after
actual normalized Jacquet restriction of `A`. No cuspidal-support sign has
been applied. All subsets occur; the empty-root-set case has its single
term of sign `+1`.

This target is generic in actual subgroup data. Identifying those data with
the standard rational-point parabolics of a connected reductive group,
proving the named representation-theoretic prerequisites, and proving this
equality remain separate obligations. In particular, arbitrary supplied
subgroup families are not asserted to satisfy involutivity. No split,
quasisplit, characteristic-zero or positive-rank restriction is added.

Source: registered original `aubert-1995-duality`, SHA256
`57af9c46769f6edd8e142ddaf465e89acfa2f2147db222d26879a28a06df9693`,
Definition 1.5 and Theorem 1.7(3), printed p.2181 / PDF p.3.
The 1996 erratum's unresolved Proposition 3.2 is not a premise or evidence
for this target.
