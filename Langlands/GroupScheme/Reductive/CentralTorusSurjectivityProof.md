# A central torus and the derived subgroup cover a connected reductive group

Authors: Worker 1383 and Worker 1408.

`Langlands.GroupScheme.reductiveCentralTorusSurjectivity` proves exactly the
published proposition
`Langlands.GroupScheme.ReductiveCentralTorusSurjectivityStatement.{u}`
(module
[`CentralTorusSurjectivityStatement`](CentralTorusSurjectivityStatement.md)),
at every universe `u`, with no hypotheses.

For every field `k : Type u`, every connected reductive group scheme `G` over
`Spec k`, and every actual derived-subgroup inclusion `d : D ⟶ G`
(`IsDerivedSubgroup d`), it gives a commutative group scheme `Z` and a
homomorphism `i : Z.toGrp ⟶ G` such that the structure morphism of `Z` is
affine and locally of finite type, `Z` is a torus, `i` is a closed central
subgroup inclusion, and the underlying map of topological spaces of
`subgroupProductMap i d : Z.toGrp.X ⊗ D.X ⟶ G.X` is surjective. The field
is arbitrary: the theorem covers imperfect fields and every characteristic.

## Implemented proof

The Lean proof is one application. The published reduction
`reductiveCentralTorusSurjectivity_of_semisimpleQuotient`, from
[`CentralTorusSurjectivityReduction`](CentralTorusSurjectivityReduction.md),
has type

`ReductiveCentralTorusSemisimpleQuotientStatement.{u} →
SemisimplePerfectStatement.{u} → ReductiveCentralTorusSurjectivityStatement.{u}`.

It is a proof-producing `def`, used here like a theorem. The proof supplies
its two hypotheses with published unconditional theorems at the same
universe `u`:

- `reductiveCentralTorusSemisimpleQuotient`, from
  [`CentralTorusSemisimpleQuotientProof`](CentralTorusSemisimpleQuotientProof.md),
  proves `ReductiveCentralTorusSemisimpleQuotientStatement`. Every connected
  reductive field group has a closed central torus `j : Z ⟶ G`, affine and
  locally of finite type, such that every affine, locally finite type fppf
  quotient of `G` by the range of `j` is semisimple.
- `semisimplePerfect`, from
  [`SemisimplePerfectProof`](../Derived/SemisimplePerfectProof.md), proves
  `SemisimplePerfectStatement`: the full derived subgroup functor of every
  semisimple field group is top.

The reduction (described in detail in its own Markdown) takes the torus `Z`
and inclusion `j` from the first hypothesis and forms the actual smooth
quotient `q : G ⟶ Q` by the range of `j` with `SmoothNormalQuotient.ofClosedNormal`.
`Q` is affine by `affineGroupSchemeQuotient`, so it is semisimple and, by the
second hypothesis, perfect. The helper
`IsDerivedSubgroup.surjective_comp_of_derivedSubgroup_eq_top` (module
[`PerfectQuotientImage`](../Derived/PerfectQuotientImage.md)) then makes
`d ≫ q` surjective. The helper `surjective_subgroupProductMap_of_isFppfQuotient`
(module [`CentralTorusProductSection`](CentralTorusProductSection.md)) turns
this into surjectivity of `subgroupProductMap j d`. The first five conjuncts
of the target are the properties of `Z` and `j` from the first hypothesis.

## Relation to the literature

The route follows J. S. Milne, *Algebraic Groups* (2017), Proposition 12.46(b)
(printed pp.245–246), applied to the central torus of Corollary 17.62(b),(d)
(printed pp.372–373), with perfectness of the semisimple quotient from
Corollary 21.50 (printed p.440). The proofs of the two hypotheses follow their
own routes, recorded in their Markdown.

## Axioms

`lean_check` reports only `propext`, `Classical.choice` and `Quot.sound`.
