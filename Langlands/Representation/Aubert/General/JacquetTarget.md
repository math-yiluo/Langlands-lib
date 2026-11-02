# Longest-representative Jacquet compatibility for the general Aubert operator

Author: Worker 165, task `e3d69272-2599-4a08-a934-cb11f2493e30`.

`Langlands.Aubert.General.JacquetCompatibilityStatement` is the separate
Prop target for the second equation of Aubert 1995, Theorem 1.7(2), printed
p.2181 / PDF p.3:
`r_J ∘ D_G = Ad(w_J) ∘ D_(M_J') ∘ r_J'`.
Here `w_J` is the longest member of `D(J,∅)`, and `J' = w_J⁻¹(J)`,
as specified on printed p.2180. This file proves no instance of the K0
identity.

The ambient group is locally compact and nonarchimedean. The finite simple
index type can be empty. `P`, `M`, `U` are actual subgroup families, with
their semidirect decompositions, closed radicals and the explicit named
`ParabolicFiniteLength` prerequisites at universe `max uG uV`. For every
Levi, closedness `hM`, the decompositions `hLevi` of the restricted
subgroups inside it and their `ParabolicFiniteLength` prerequisites
`hLeviFl` are visible. These are the same actual families and Levi operators
used by [`InductionTarget`](InductionTarget.md).

The indexing group is the actual quotient `N_G(T)/Z_G(T)`, defined with the
full centralizer. It has a supplied `Fintype` and an
`ActualCoxeterSystem T CM`; the Weyl elements are actual quotient classes,
rather than independent labels. `longestRep actual J` is the constructed
maximum-length member of the minimum-representative set `D(J,∅)`.
`associatedSubset actual J` uses its inverse on simple reflections.
Identification with the relative roots, including the sign of each simple
root, and uniqueness of the longest representative remain explicit
realization/proof obligations of this generic layer.

The prerequisite `hAssociated` is the separately named proposition
`RelativeWeylIndexing.actualAssociatedLeviConjugation T M actual`:
for every normalizer lift `n` of this longest representative,
`n M_(J') n⁻¹ = M_J` as equality of actual subgroup images.
It contains no K0 identity. The elementary helper
`conjugationMembership_of_map_eq` converts that image equality to
`x ∈ M_J ↔ n⁻¹ x n ∈ M_(J')`. Its proof writes membership in the image
as an actual preimage and cancels the conjugations in both directions.

The transport in the target is exactly Worker 23's
`conjugationK0 n` from [`AlternatingOperator`](AlternatingOperator.md),
using this derived membership equivalence. It sends a representation of
`M_(J')` to one of `M_J` by pullback along the continuous equivalence
`x ↦ n⁻¹ x n`, and it sends its exact class to the actual transported
class. Thus forward subgroup conjugation goes from `J'` to `J`, and
representation transport uses the inverse map. The target quantifies
every lift of the specified quotient element. It does not assume or claim
equality of elementwise conjugation maps for different lifts.

Every composition is an equality of integer-linear maps between exact
Grothendieck groups of finite-length smooth complex representations.
`r` is the map of the actual normalized Jacquet functor; `D_G` and the
Levi operator are the unadjusted signed sums of the actual induction/Jacquet
maps, with their upstream actual-representation class formulas.
There is no extra sign and no replacement of the associated subset by `J`.

This is a target on actual subgroup data, pending the connected-reductive
rational-point specialization. In addition to the named representation
prerequisites and compatibility proof, that specialization must realize the
maximal split torus, its abstract normalizer/full-centralizer quotient,
the relative-root Coxeter system, standard-Levi root identification and
associated-Levi conjugation. The scheme-morphism quotient is not
definitionally the abstract rational-point quotient. No arbitrary supplied
family or Coxeter system is asserted to satisfy these identifications or the
target. No split, quasisplit, characteristic-zero or positive-rank
restriction is added.

Sources:

- Registered original `aubert-1995-duality`, SHA256
  `57af9c46769f6edd8e142ddaf465e89acfa2f2147db222d26879a28a06df9693`,
  printed p.2180 / PDF p.2 for `w_J` and `J'`, Definition 1.5 and the
  second equation of Theorem 1.7(2), printed p.2181 / PDF p.3.
- Registered original `renard-2026-representations-groupes-reductifs-padiques`,
  SHA256 `7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`,
  V.4.1 and V.4.3, printed pp.118–119 / PDF pp.124–125, for the
  full-centralizer quotient, actual Levi embedding and forward subgroup
  conjugation. The helper converting image equality to membership is
  internal elementary group theory.
