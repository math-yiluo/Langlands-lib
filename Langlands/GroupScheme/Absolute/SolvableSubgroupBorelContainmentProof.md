# Proof that a Borel contains each given smooth connected solvable subgroup

Author: Worker 1095.

The module proves

```
theorem Langlands.GroupScheme.solvableSubgroupBorelContainment :
    SolvableSubgroupBorelContainmentStatement.{u}
```

for the published proposition of
`Langlands.GroupScheme.Absolute.SolvableSubgroupBorelContainmentStatement`, at
arbitrary universe `u` and in every characteristic. Fix an algebraically closed
field `k`, a smooth affine group scheme `G` over `Spec k` with connected
underlying space, and a closed subgroup embedding `j : H ⟶ G` whose source is
smooth, connected and solvable (`IsSolvableGroupScheme H`). The theorem gives a
group scheme `B`, an embedding `i : B ⟶ G` with `IsBorelSubgroup i`, and an
actual homomorphism `f : H ⟶ B` with `f ≫ i = j`. The given `j` itself is kept;
it is not replaced by a conjugate or by another subgroup.

## The Lean proof

After introducing the data and hypotheses of the proposition, the proof is one
application of the published theorem
`Langlands.GroupScheme.BorelExistence.exists_isBorelSubgroup_containing`
(module `Langlands.GroupScheme.Absolute.BorelContaining`). That theorem takes
any field, an ambient group with `IsAffineHom G.X.hom` and
`LocallyOfFiniteType G.X.hom`, and a homomorphism `a : H ⟶ G` with
`BorelExistence.IsAdmissible a`. Its conclusion is literally the conclusion of
the target proposition with `a := j`.

`IsAdmissible j` is the conjunction
`IsClosedSubgroup j ∧ Smooth H.X.hom ∧ ConnectedSpace H.X.left ∧ IsSolvableGroupScheme H`.
The proof supplies the hypothesis `IsClosedSubgroup j`, the two instance
arguments `Smooth H.X.hom` and `ConnectedSpace H.X.left` (by
`inferInstance`), and the hypothesis `IsSolvableGroupScheme H`.
`IsAffineHom G.X.hom` is an instance argument of the proposition.
`LocallyOfFiniteType G.X.hom` comes from `Smooth G.X.hom` by Mathlib's
instances: smooth implies locally of finite presentation, which implies locally
of finite type.

## The imported argument

`exists_isBorelSubgroup_containing` (Worker 1358) is the restricted
minimization described in this task's context. Let `Q n` say that some
admissible `i : B ⟶ G` has a factor `f : H ⟶ B` with `f ≫ i = j`, and that
`(coordinateKernel i).height.toNat = n`. Here `coordinateKernel i` is the
kernel of the map `Γ(G, ⊤) → Γ(B, ⊤)` of global sections. `Q` holds for some
`n`, with `B = H`, `i = j` and the identity factor. `Nat.find` chooses an
admissible `i : B ⟶ G` with a factor `f` of minimal height.

To prove `IsBorelSubgroup i`, the remaining field is maximality. Suppose
`i' : B' ⟶ G` is admissible and `g : B ⟶ B'` satisfies `g ≫ i' = i`. Then
`f ≫ g` is a factor of `j` through `i'`, so `Q` holds at the height of `i'` and
minimality gives height(`i`) ≤ height(`i'`). These heights are finite by
`BorelExistence.coordinateKernel_height_ne_top` (the coordinate ring of `G` is
Noetherian and the kernel is prime). From this inequality,
`BorelExistence.isIso_of_coordinateKernel_height_le`
(module `Absolute.BorelExistenceCoordinates`) shows that `g` is an
isomorphism, which is the maximality required by `IsBorelSubgroup`.

## Use of the hypotheses

- `IsAffineHom G.X.hom`, and `Smooth G.X.hom` only through
  `LocallyOfFiniteType G.X.hom`: the imported theorem needs both properties.
- `Smooth H.X.hom`, `ConnectedSpace H.X.left`, `IsClosedSubgroup j`,
  `IsSolvableGroupScheme H`: together they are `IsAdmissible j`.
- `IsAlgClosed k` and `ConnectedSpace G.X.left`: not used. The imported
  theorem holds over any field and for any affine ambient group locally of
  finite type.

No conjugacy theorem for Borel subgroups or maximal tori is used or imported as
a hypothesis. The proof also uses no maximal-torus existence, root datum or
reductivity. Axioms: `propext`, `Classical.choice`, `Quot.sound`.

## Dependencies and provenance

Library: `Langlands.GroupScheme.Absolute.SolvableSubgroupBorelContainmentStatement`
(the target, with `IsBorelSubgroup`, `IsClosedSubgroup` and
`IsSolvableGroupScheme` through `Absolute.Borel`) and
`Langlands.GroupScheme.Absolute.BorelContaining`
(`BorelExistence.exists_isBorelSubgroup_containing`, which uses
`Absolute.BorelExistence` and `Absolute.BorelExistenceCoordinates`). Mathlib:
the `Smooth` and `LocallyOfFinitePresentation` instances of
`Mathlib.AlgebraicGeometry.Morphisms`.

Milne, *Algebraic Groups* (2017), source `milne-2017-algebraic-groups`, defines
a Borel subgroup as a maximal connected solvable subgroup variety (Definition
17.6, printed p.353). The next remark (printed p.354) says that a connected
solvable subgroup variety of largest possible dimension is a Borel subgroup.
The proof of Theorem 17.10 (printed p.355) states without further detail that
maximal tori, being smooth, connected and solvable, lie in Borel subgroups.
The Lean proof makes this step explicit. It does not use the
largest-dimension remark. Instead it takes, among the admissible subgroups
through which the given `j` factors, one whose coordinate kernel has least
height. Minimal height replaces maximal dimension.
