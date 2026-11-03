# Rational conjugation of split solvable subgroups into pseudo-parabolics

Author: Worker 274.

`Langlands.GroupScheme.SplitSolvableIntoPseudoParabolicStatement.{u}` is
the full split-solvable containment assertion of Conrad–Gabber–Prasad,
*Pseudo-reductive groups*, second edition (2015), Lemma C.2.2, printed p.593
(PDF p.619). The registered source is
`conrad-gabber-prasad-2015-pseudo-reductive`, SHA-256
`1b77af44c90211db9a3efa50896a3722f4fd2df332b7ce2ec52202eb243e7f54`.
This file supplies an unproved proposition definition.

For every field `k : Type u`, take an actual smooth connected affine group
scheme `G` over `Spec k` and a pseudo-parabolic inclusion `i : P ⟶ G`.
For every actual closed subgroup `j : H ⟶ G` such that
`IsSplitSolvableGroupScheme H`, the conclusion supplies a single rational
point `g` of `G` over `k` and an actual group-scheme homomorphism
`f : H ⟶ P` with

```text
f ≫ i = j ≫ (G.innerIso g).hom.
```

The imported split-solvable predicate requires smoothness, connectedness,
affineness and solvability, together with a finite normal series whose
represented fppf quotients are one-dimensional vector groups or copies of
the multiplicative group over `k`. Normality, triviality and the quotient
conditions concern every relative scheme test. This is the project's
explicit meaning of the source's split solvable smooth connected subgroup.
The conclusion is an equality of actual group-scheme homomorphisms and
therefore identifies the conjugated inclusion on every relative scheme
test, including its scheme structure.

The source writes conjugation as `g⁻¹ H g`. The published `innerIso g`
acts as `x ↦ g x g⁻¹`, so replacing the source's rational point by its
inverse gives the displayed convention. The existential assertion is
unchanged. This statement imposes no reductivity, pseudo-reductivity,
perfection, characteristic or splitting assumption on `G` or `k`.
All objects and relative scheme tests are in the arbitrary universe `u`.

The source proof applies the split-solvable fixed-point theorem to the
left action on `G/P`, using pseudo-completeness, and then lifts the fixed
rational coset to `G(k)`. None of these geometric inputs is proved here.
The existing `SplitTorusIntoPseudoParabolicStatement` concerns only split
tori; it is a narrower target and does not prove this statement. This
statement also leaves the existence of the split solvable subgroup
`S ⋉ R_us,k(P)` used in Theorem C.2.5 as a separate obligation.
