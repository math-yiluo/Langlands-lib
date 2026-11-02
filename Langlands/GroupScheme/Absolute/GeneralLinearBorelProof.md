# Proof of the `GL_N` Borel statement

Authors: Worker 1234 and Worker 308. Worker 1234 wrote this module and the
coordinate module `Langlands.GroupScheme.Absolute.GeneralLinearBorelCoordinates`.
Worker 308 wrote the point-group modules `Langlands.Group.GL.UpperTriangularSolvable`,
`Langlands.Group.GL.OppositeRootNonsolvable` and
`Langlands.Group.GL.UpperTriangularMaximalSolvable` used here.

`Langlands.GroupScheme.generalLinearBorel` proves the published proposition
`Langlands.GroupScheme.GeneralLinearBorelStatement` (module
`Langlands.GroupScheme.Absolute.BorelStatement`). For every field `k : Type u`,
every `N : ℕ` and every strictly decreasing `e : Fin N → ℤ`, with
`R = CommRingCat.of k`:

1. `GeneralLinear.blockParabolicHom (Fin N) R e`, the upper triangular subgroup
   scheme, is a Borel subgroup of `GL_N` (`IsBorelSubgroup`);
2. with the diagonal torus it forms a Borel pair (`IsBorelPair`);
3. it represents `Dynamic.parabolic` of `GeneralLinear.diagonalCocharacter (Fin N) R e`;
4. the cocharacter of the diagonal torus with coordinates `e` is regular
   (`IsRegularCocharacter`).

Sources of the statement: Milne, *Algebraic Groups* (2017), source ID
`milne-2017-algebraic-groups`, Example 17.7 (printed p.354, PDF p.370: the
Borel subgroups of `GL_V`) and Proposition 21.29 (printed p.433, PDF p.449:
`P(λ)` is a Borel subgroup for regular `λ`). Milne's Example 17.7 works over an
algebraically closed field and uses the Lie–Kolchin theorem. The Lean proof
below takes a different, internal route: maximality over `k` is reduced to
`k̄`-points of a reduced scheme, and on `k̄`-points to the abstract group theory
of Worker 308's modules. The proof has no restriction on the characteristic, and
`N = 0` is allowed.

All helper declarations are in the namespace
`Langlands.GroupScheme.GeneralLinear.UpperTriangular`.

## Points of the upper triangular subgroup

Write `pointsEquiv (Fin N) R T` for the published identification of the points
of `GL_N` over a test scheme `T` with `GL (Fin N) Γ(T, ⊤)`, and
`upperTriangularSubgroup N A` for the published subgroup of upper triangular
invertible matrices (`Langlands.GeneralLinear`).

- `pointsEquiv_mem_upperTriangularSubgroup` and
  `mem_blockParabolic_of_mem_upperTriangularSubgroup`: for strictly decreasing
  `e`, a point of `GL_N` lies in the published block parabolic subgroup functor
  `blockParabolic (Fin N) R e` exactly when its matrix is upper triangular.
  The published `mem_blockParabolic` asks for vanishing of the entries `(a, b)`
  with `e a < e b`, that is, with `b < a`.
- `isSolvable_points`: over every test scheme `T`, the group of points of
  `blockParabolicScheme (Fin N) R e` is solvable. The published
  `isRepresentedBy_blockParabolic` identifies it with the points of the functor,
  hence by the previous item with a subgroup of
  `upperTriangularSubgroup N Γ(T, ⊤)`. That group is solvable by Worker 308's
  `UpperTriangularSolvable.isSolvable` (any commutative ring), and the
  injective homomorphism transfers solvability
  (`Group.isSolvable_of_isSolvable_injective`).
- `exists_diagonalTorus_factor`: the published diagonal torus
  `diagonalTorus (Fin N) R` factors through `blockParabolicHom (Fin N) R e`.
  Its points have diagonal matrices (`pointsEquiv_diagonalTorus_val`), which
  lie in the block parabolic functor. The published
  `SubgroupFunctor.IsRepresentedBy.lift` turns the resulting inclusion of point
  groups into a homomorphism of group schemes, and `lift_comp_eq` shows that it
  composes to the diagonal torus.

## Transport of maximal solvability

`le_upperTriangularSubgroup_of_ringEquiv`: let `ψ : A ≃+* F` be a ring
isomorphism to an infinite field and `H` a solvable subgroup of `GL (Fin N) A`
containing the upper triangular matrices. Then `H` consists of upper
triangular matrices. Map `H` to `GL (Fin N) F` along `ψ`; the image is
solvable and contains the upper triangular group, so it equals that group by
Worker 308's `UpperTriangularMaximalSolvable.eq_upper_of_isSolvable` (which
needs `Infinite F`). Pulling back along `ψ` keeps entries zero. This is used
with `A = Γ(Spec k̄, ⊤)` and `F = k̄ = AlgebraicClosure k`, via the published
`Scheme.ΓSpecIso`.

## The Borel subgroup

- Smoothness and connectedness: `smooth_blockParabolicScheme` and
  `connectedSpace_blockParabolicScheme` from the coordinate module.
- `isSolvableGroupScheme_blockParabolicScheme`: the published
  `IsSolvableGroupScheme` asks for solvability of the `k̄`-points of the base
  change to `k̄`. The published `baseChangePointsEquiv` identifies these with
  the points of `blockParabolicScheme (Fin N) R e` over `Spec k̄ ⟶ Spec k`
  (`closurePoint k`), which form a solvable group by `isSolvable_points`.

Maximality is proved for a closed subgroup `i' : B' ⟶ GL_N` with `B'` smooth
and solvable, and `f` from the upper triangular subgroup scheme with
`f ≫ i' = blockParabolicHom (Fin N) R e`. Connectedness of `B'` is not used.

- `closurePoint_mem`: every point of `B'` over `closurePoint k` maps to an
  upper triangular matrix. The image `ρ.range` of these points in
  `GL (Fin N) Γ(Spec k̄, ⊤)` is solvable: by `baseChangePointsEquiv` the points
  are those of the base change, solvable by the hypothesis. The image contains
  every upper triangular matrix, since such a matrix is a point of the upper
  triangular subgroup scheme, mapped into `B'` by `f`. By
  `le_upperTriangularSubgroup_of_ringEquiv` the image is upper triangular.
- `universal_mem`: the universal point `i'.hom.hom` of `B'` lies in the block
  parabolic functor. For each entry `(a, b)` with `b < a`, compare two
  morphisms from `B'` to the affine line over `k`: the one given by the entry
  `s` (through the published `AffineLine.homEquiv`) and the zero one. `B'` is
  reduced, as a smooth scheme over a field (the published
  `SmoothReducedProof.isReduced_of_smooth_over_field`), and flat and locally of
  finite type over `k`; the affine line is separated. The published
  `SchemeHomOver.ext_of_forall_algebraicClosure_point_of_isReduced_of_flat`
  (with base ring and fraction field `k`, algebraic closure `k̄`) reduces the
  equality to `k̄`-points. At a `k̄`-point `x` the entry `s` pulls back to the
  entry `(a, b)` of the matrix of `x ≫ i'` (`pointsEquiv_comp_apply`,
  `AffineLine.homEquiv_comp`), which vanishes by `closurePoint_mem`. So the
  two morphisms agree, and `s = 0`.
- `isIso_of_comp_eq_blockParabolicHom`: `f` is an isomorphism. Since `i'` is a
  closed immersion, it is a monomorphism, so it represents its range. By
  `universal_mem` and the published `comp_mem`, the range of `i'` lies in the
  block parabolic functor. The published `IsRepresentedBy.lift` then gives
  `g : B' ⟶ blockParabolicScheme (Fin N) R e` with
  `g ≫ blockParabolicHom (Fin N) R e = i'`. Both composites `f ≫ g` and
  `g ≫ f` are identities, checked after the monomorphisms with the published
  `IsRepresentedBy.hom_ext`.
- `isBorelSubgroup_blockParabolicHom` assembles these into
  `IsBorelSubgroup (blockParabolicHom (Fin N) R e)`, using the published
  `isClosedSubgroup_blockParabolicHom`.

## Regularity

`isRegularCocharacter_diagonalTorus`: by the published `roots_diagonalTorus`
every root of the diagonal torus has character coordinates
`single a 1 - single b 1` with `a ≠ b`. The published
`splitTorus.latticePairing_eq_sum` computes its pairing with the cocharacter of
coordinates `e` as `e a - e b`, which is nonzero because a strictly decreasing
function is injective.

## The theorem

`generalLinearBorel` combines:

1. `isBorelSubgroup_blockParabolicHom`;
2. the Borel pair from part 1, the published `isMaximalTorus_diagonalTorus`
   (module `Reductive.GeneralLinearMaximal`) and `exists_diagonalTorus_factor`;
3. the published `isRepresentedBy_parabolic_diagonalCocharacter`;
4. `isRegularCocharacter_diagonalTorus`.

The theorem has the exact target statement as its type, with no additional
hypotheses.
