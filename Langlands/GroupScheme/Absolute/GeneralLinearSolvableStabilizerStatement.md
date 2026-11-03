# A proper `GL_N`-scheme with solvable point stabilizers

Worker 1396.

`Langlands.GroupScheme.GeneralLinearSolvableStabilizerStatement.{u}` is a
definition returning `Prop`. This module supplies no proof of it.

For every `k : Type u` with `Field k` and `IsAlgClosed k`, and every `N : ℕ`,
write `S = Spec (CommRingCat.of k)` and
`GL = GeneralLinear.groupScheme (Fin N) (CommRingCat.of k)`. The proposition
asserts that there are `X : Over S` and an action `a : SchemeAction GL X` such
that

- `X.hom` is proper and `X.left` is nonempty;
- for every rational point `x : 𝟙_ (Over S) ⟶ X`, every
  `H : GroupScheme S` and every homomorphism `i : H ⟶ GL` with
  `IsClosedSubgroup i`, if `x` is fixed by the restricted action
  `a.restrict i` (`SchemeAction.IsFixed`, fixedness after every change of test
  scheme), then `IsSolvableGroupScheme H`.

`IsSolvableGroupScheme H` is the Library's notion: the abstract group of points
of `H` over the algebraic closure of `k` is solvable.

Provenance (derived). The intended witness is the scheme of full flags in
`k^N`. Milne, *Algebraic Groups* (2017), registered as
`milne-2017-algebraic-groups`, Proposition 7.29, printed p.146 (one-based PDF
p.162), shows that for a flag `F` in a finite-dimensional vector space `V` the
quotient `GL_V / B(F)` by the stabilizer `B(F)` of `F` represents the functor of
flags of the same type. Proposition 7.30 on the same page shows that flag
varieties are projective, hence proper. For a full flag, `B(F)` is a conjugate
of the group `T_N` of upper triangular matrices, which is solvable by Example
6.28, printed p.132 (PDF p.148). A closed subgroup fixing a rational point `x`
lies in the stabilizer of `x`, which is a conjugate of `T_N`. So its group of
points over the algebraic closure of `k` is a subgroup of a group of invertible
upper triangular matrices, and is therefore solvable. The proposition records
only these properties of the flag scheme: properness, nonemptiness, and the
solvability of closed subgroups fixing a point. It does not name the scheme.
For `N = 0` the group `GL_0` is trivial and the flag scheme is a point.
