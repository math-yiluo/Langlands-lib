# Smooth fixed subgroups for diagonalizable actions

`Langlands.GroupScheme.Diagonalizable.FixedSubgroupSmoothStatement.{u}`
is the smoothness part of Conrad–Gabber–Prasad, *Pseudo-reductive Groups*,
second edition (2015), Proposition A.8.10(2), printed pp. 547–550
(PDF pp. 573–576), specialized to automorphic actions on smooth affine groups
over a field.

The actor is the actual group scheme
`Diagonalizable.groupScheme (CommRingCat.of k) Λ = D(Λ)`, represented by
the group algebra `k[Λ]`. The character group `Λ` is a finitely generated
abelian group. It may have torsion; the actor need not be smooth or reduced.
In particular, the statement includes diagonalizable groups with torsion
divisible by the characteristic. Such groups are linearly reductive:
their representations are graded by `Λ`, and taking the degree-zero
summand is exact. Finite generation supplies the finite-type hypothesis
on the actor in the cited proposition.

For every automorphic action on a smooth affine `k`-group `G`, and every
closed immersion `j : C ⟶ G` representing its fixed subgroup on all test
schemes, the conclusion is `Smooth C.X.hom`. Fixedness is the existing
`AutomorphicAction.fixedSubgroup`, which tests the action after every
scheme refinement. It therefore retains the infinitesimal information in
nonsmooth actors.

This is a statement, not a proof. Existence of the closed representative
is an explicit premise; general closed representability is a separate
result. The conclusion asserts smoothness only. It imposes no connectedness
condition and asserts no Lie-space comparison. This form can be used after
identifying a torus-character kernel with `D(X*(S)/ℤa)` without discarding
the torsion in that quotient.
