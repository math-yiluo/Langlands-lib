# Reduction of the central-intersection finiteness to an algebraic closure

Author: Worker 846. The interface of the algebraically closed input was
proposed by Worker 1408.

This module reduces `DerivedCentralIntersectionFinitenessStatement.{u}` to one
assertion over algebraically closed fields, which is taken as the explicit
hypothesis `hfin`. It proves no finiteness over an algebraically closed field.
Let `K = AlgebraicClosure k` and let `b = toAlgebraicClosure k : Spec K ⟶ Spec k`.

## Auxiliary lemmas

- `SubgroupFunctor.comap_baseChange`: for any base change `b : S' ⟶ S`, any
  homomorphism `f : H ⟶ G` and any subgroup functor `F` of `G`,
  `(F.comap f).baseChange b = (F.baseChange b).comap ((GroupScheme.baseChange b).map f)`.
  The proof checks membership on each test scheme, using
  `baseChangePointsEquiv_comp`.
- `finite_left_of_finite_pullback`: if `X` is over `Spec k` and the pullback of
  `X.hom` along `b` has finitely many points, then so does `X.left`. Here `b`
  is surjective, because `Spec k` has one point and `Spec K` is nonempty. So
  the first projection of the pullback is surjective, by stability of
  surjectivity under base change.
- `isFinite_hom_of_finite_left`: if `X.hom` is locally of finite type and
  quasi-compact and `X.left` is finite, then `X.hom` is finite. Finite fibres
  make `X.hom` locally quasi-finite
  (`LocallyQuasiFinite.of_finite_preimage_singleton`). `Spec k` is locally
  Artinian, so Mathlib's `IsFinite.of_locallyQuasiFinite` applies.
- `isFinite_of_finite_pullback`: let `c : C ⟶ D` and `d : D ⟶ G` be closed
  subgroups over `Spec k`, with `G.X.hom` locally of finite type and
  quasi-compact. If the base change of `C.X.hom` along `b` has finitely many
  points, then `C.X.hom` is finite. The structure map of `C` is
  `c ≫ d ≫ G.X.hom` (by `Over.w`). Closed immersions are of finite type and
  quasi-compact, so the two previous lemmas apply.

## The conditional theorem

`derivedCentralIntersectionFiniteness_of_algClosed` assumes the hypothesis
`hfin`. Let `K` be any algebraically closed field in universe `u`, and let
`d : D ⟶ G` and `s : S ⟶ D` be homomorphisms of group schemes over `Spec K`.
Assume that `G.X.left` is affine, that `G.X.hom` is locally of finite type,
that `HasTrivialUnipotentRadical G` holds, that `d` is a derived-subgroup
inclusion and that `s` is a closed subgroup. If
`SubgroupFunctor.range s ≤ (center G).comap d`, then `S.X.left` has finitely
many points. From this the theorem proves
`DerivedCentralIntersectionFinitenessStatement.{u}`.

The proof applies
`derivedCentralIntersectionFiniteness_of_isFinite_subgroupIntersection`
(module `Langlands.GroupScheme.Derived.CentralIntersectionPullback`). Fix `k`,
a connected reductive `G`, a derived-subgroup inclusion `d : D ⟶ G` and a
centre representative `z`. Let `C = subgroupIntersection d z` and
`c = subgroupIntersectionFst d z`. It remains to prove that `C.X.hom` is
finite. Apply `hfin` with `K = AlgebraicClosure k` to the base changes
`G_K`, `d_K` and `c_K` along `b`. The hypotheses are checked as follows.

- `G_K.X.left` is the pullback of the affine morphism `G.X.hom` to the affine
  scheme `Spec K`, hence affine. Its structure map is locally of finite type,
  since `G.X.hom` is smooth.
- `HasTrivialUnipotentRadical G_K` is the field
  `hasTrivialGeometricUnipotentRadical` of `IsConnectedReductive G`.
- `IsDerivedSubgroup d_K` is the first part of the published
  `derivedSubgroupFieldBaseChange` for the extension `K / k`.
- `c_K` is a closed subgroup by `IsClosedSubgroup.baseChange`.
- The range of `c_K` equals `(center G_K).comap d_K`. Rewrite with
  `SubgroupFunctor.range_baseChangeHom`, then with the range equality
  `range c = (center G).comap d`, then with `SubgroupFunctor.comap_baseChange`,
  and finally with the published `center_baseChange`.

So `hfin` makes the pullback of `C.X.hom` along `b` finite. Then
`isFinite_of_finite_pullback` for the closed subgroups `c` and `d` gives
finiteness of `C.X.hom`. Here `G.X.hom` is smooth, hence locally of finite
type, and affine, hence quasi-compact.

The universe `u` stays arbitrary. Imperfect fields and positive characteristic
are allowed, and no assumption is placed on `D` or `d` beyond the target's
premises. The descent uses only the number of points of `C`. Finiteness of the
structure morphism is then a statement about the full scheme `C`, so its
nonreduced structure is kept. The argument does not use
`DerivedSubgroupSemisimpleStatement` or `IsSemisimple D`.
