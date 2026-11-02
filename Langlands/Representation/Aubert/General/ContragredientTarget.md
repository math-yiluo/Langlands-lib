# General Aubert operator and smooth contragredients

Author: Worker 165, task `e3d69272-2599-4a08-a934-cb11f2493e30`.

`Langlands.Aubert.General.ContragredientCommutationStatement` is the separate
Prop target for Aubert 1995, Theorem 1.7(1), printed p.2181 / PDF p.3:
`D_G ∘ c_G = c_G ∘ D_G`. Here `c_G` is the actual smooth contragredient on
the exact finite-length smooth Grothendieck group. This file proves no instance
of the target.

The supplied group has `Group`, `TopologicalSpace`, `LocallyCompactSpace` and
`NonarchimedeanGroup` structures. A finite index type supplies all simple-root
subsets, including the empty set. The families `P`, `M`, `U` consist of actual
subgroups; `h` supplies their semidirect decompositions and `hU` the closedness
of each `U`. `hfl` is the named `ParabolicFiniteLength` prerequisite for every
decomposition, at the saturated carrier universe `max uG uV`. It includes
finite-length preservation and exactness on finite-length short exact sequences
for both actual normalized functors.

The two maps in the equality are exactly those of
[`AlternatingOperator`](AlternatingOperator.md), authored by Worker 23:
`alternatingOperator P M U h hU hfl` is the unadjusted sum
`∑_I (-1)^|I| i_I r_I`, and `contragredientK0 G hcof hc` is induced by the
actual smooth contragredient. Its visible prerequisites are compact-open
cofinality `hcof` and `ContragredientPreservesFiniteLength` `hc`.
The upstream class formulas identify their values as the classes of the actual
functors on finite-length smooth representations. The proposition is equality
of integer-linear maps on the whole exact Grothendieck group.

This is the generic actual-subgroup target layer. It does not identify the
families with the standard parabolics of a connected reductive group, nor
establish the named representation-theoretic prerequisites. Those actual
realizations and the proof of this equality remain required. No characteristic,
splitness, quasisplitness or positive-rank assumption is imposed here; this
absence does not itself construct the nonarchimedean rational-point instance.

Source: registered original `aubert-1995-duality`, SHA256
`57af9c46769f6edd8e142ddaf465e89acfa2f2147db222d26879a28a06df9693`,
Theorem 1.7(1), printed p.2181 / PDF p.3, with Definition 1.5 on the same
page and the normalized-functor conventions on printed p.2180. The
contragredient construction and its prerequisites are documented in the
upstream module. The 1996 erratum concerns the later irreducibility argument
and supplies no proof of this target.
