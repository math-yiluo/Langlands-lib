# The projective linear torus fixed-point dimension bound

`Langlands.GroupScheme.projectiveTorusFixedPointDimension` proves the Library proposition
`Langlands.GroupScheme.ProjectiveTorusFixedPointDimensionStatement.{u}` (Milne, *Algebraic
Groups* (2017), Proposition 20.11, printed pp. 410–411, PDF pp. 426–427). It keeps the
statement's full scope at universe `u`:

- `k` is any algebraically closed field, of any characteristic;
- `T` is a split torus;
- `X` is any nonempty reduced finite-type scheme over `Spec k`, possibly reducible;
- `a` is the action, `ρ` the matrix representation, and `φ` the matrix-equivariant closed
  immersion into `ProjectiveOrbit.ambient n`.

The conclusion is the statement's own: for every natural `d` with
`d ≤ topologicalKrullDim X.left` there is an injective family `Fin (d + 1) → (pt ⟶ X)` of
rational sections, each fixed in the all-test sense `SchemeAction.IsFixed`. Here `pt` is the
base test `Over.mk (𝟙 (Spec k))`. The proof adds no hypothesis.

This module only assembles two helper results proved in this submission.

1. `SplitTorusGenericWeights.exists_genericWeights hT ρ`, in
   `Langlands.GroupScheme.SplitTorusGenericWeights`, chooses coordinates and a cocharacter.
   It gives `P : GL (Fin (n + 1)) k` and integral weights `m : Fin (n + 1) → ℤ` such that:
   - for every `z : kˣ`, some rational point of `T` acts by `P · diag(z ^ m i) · P⁻¹`;
   - every rational point of `T` acts by `P · diag(χ) · P⁻¹` for some `χ` that is constant
     on each level set of `m`.

   These are Milne's eigenvector basis and his "suitably chosen cocharacter".
2. `ProjectiveTorusFixedPoint.exists_fixed_points_of_frame`, in
   `Langlands.GroupScheme.ProjectiveTorusFixedPointTransfer`, holds for a smooth group scheme
   `H` over `Spec k` with `k` algebraically closed. From such a frame `(P, m)` for a
   representation of `H`, it produces the required injective family of fixed rational points
   of `X`. It applies the counting result `ProjectiveSpace.exists_weightBlock_points` (module
   `Langlands.AlgebraicGeometry.ProjectiveSpace.WeightBlockPoints`) to the image of `X` in
   the coordinates given by `P`. Each point it obtains has coordinates in one weight block,
   and is lifted to a rational point of `X`. The module then passes from fixedness under
   rational points to all-test fixedness, using the smoothness of `H`.

Proof. Introduce the statement's variables. A split torus is smooth (`IsSplitTorus.smooth`),
which supplies the smoothness instance that theorem 2 needs. Then apply theorem 1 to `ρ`,
and pass its frame to theorem 2 together with `hφc`, `hφ`, `d` and `hd`. Theorem 2 needs
`LocallyOfFiniteType X.hom`, which is among the statement's hypotheses.
