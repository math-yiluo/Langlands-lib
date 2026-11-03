# Central closed subgroups of an actual derived subgroup over an algebraically closed field

Author: Worker 1408.

This module proves the algebraically closed case of the central intersection
finiteness. Its main theorem `finite_of_isAlgClosed` has exactly the shape of
the hypothesis `hfin` of `derivedCentralIntersectionFiniteness_of_algClosed`
(module `Langlands.GroupScheme.Derived.CentralIntersectionReduction`, by
Worker 846). It corresponds to the algebraically closed step of Milne,
*Algebraic Groups* (2017), Proposition 19.21(b), printed p.402. The
implementation follows the derived route described below, not the source's
central-torus argument. Namespace: `Langlands.GroupScheme.CentralIntersection`.

Throughout, `K` is an algebraically closed field in universe `u`. `G`, `D` and
`S` are group schemes over `Spec K`. `d : D ⟶ G` satisfies
`IsDerivedSubgroup d`. `s : S ⟶ D` satisfies `IsClosedSubgroup s`. The
hypothesis `hc : SubgroupFunctor.range s ≤ (center G).comap d` says that every
point of `S`, over every test scheme, maps to a central point of `G`. `G.X.left`
is affine and `G.X.hom` is locally of finite type, and `hG` is
`HasTrivialUnipotentRadical G`.

## An isolated closed point

`exists_isClosed_isOpen_singleton`: under these hypotheses, some point `x` of
`S.X.left` has `{x}` both closed and open.

Proof.

1. `d` is a closed immersion (the first field of `IsDerivedSubgroup`), so
   `s ≫ d` is a closed subgroup of `G`, and `S.X.hom` is locally of finite type.
   The published `ReducedSubgroup.exists_reducedIdentityComponent` applied to
   `s ≫ d` gives a group scheme `H` and `f : H ⟶ S`. Here `ι = f ≫ s ≫ d` is a
   closed subgroup of `G`, `H` is smooth and connected, and the image of `f` is
   open in `S.X.left`.
2. `hc` gives `IsCentral (s ≫ d)`, and so `IsCentral ι` (`IsCentral.comp`).
   Hence the range of `ι` is a normal subgroup functor: conjugating a central
   point returns it. Since `ι` is a monomorphism, any two rational points of `H`
   commute.
3. The published `affineLinearEmbeddingStatement` gives a matrix representation
   `ρ : MatrixRepresentation G (Fin N)` that is a closed subgroup. Its
   restriction `ρ.restrict ι` to `H` has underlying morphism a closed
   immersion. `H` is reduced, because it is smooth over a field
   (`SmoothReducedProof.isReduced_of_smooth_over_field`), and affine, because
   `ι` is affine and `G` is affine.
4. Let `h` be a rational point of `H`. Its image `h ≫ ι` is
   `(h ≫ f ≫ s) ≫ d`, the image of a rational point of `D`, and it is central.
   By `pow_factorial_eq_one_of_mem_roots` (module `BlockCharacter`), every
   eigenvalue `c` of the rational matrix of `h` under `ρ.restrict ι` satisfies
   `c^(N!) = 1`. This uses `MatrixRepresentation.rationalMatrix_restrict`.
5. `isUnipotent_of_eigenvalues` (module `Unipotence`) gives `IsUnipotent H`.
   Now `ι` is a closed subgroup, `H` is smooth, connected and unipotent, and
   the range of `ι` is normal. So `hG` gives `SubgroupFunctor.range ι = ⊥`.
6. The universal point `𝟙 H.X` lies in that range, so `𝟙 H.X = 1` after
   cancelling the monomorphism `ι`. Hence every point of `H.X.left` equals the
   image of the identity section. So `H.X.left` is a subsingleton, and the
   image of `f` is the single point `x₀`, the image of the identity of `S`.
7. `x₀` is closed, since it comes from a rational point
   (`pointEquivClosedPoint`). It is open, since it is the image of `f`.

## From an isolated point to finiteness

`finite_of_isOpen_singleton`: let `S` be a group scheme over `Spec K` with
`S.X.hom` locally of finite type and `S.X.left` quasi-compact. If some `x` has
`{x}` closed and open, then `S.X.left` is finite.

Proof. `S.X.left` is a Jacobson space (`LocallyOfFiniteType.jacobsonSpace`).
For any closed point `y`, the published `ReducedSubgroup.exists_translation`
gives an automorphism `β` of `S.X.left` with `β x = y`. A scheme isomorphism is
a homeomorphism (`Scheme.homeoOfIso`), so `{y}` is open. The union of all closed
points is therefore open, and its complement is closed. If the complement were
nonempty, it would contain a closed point (`nonempty_inter_closedPoints`),
which is absurd. So every point is closed, hence open, and `S.X.left` is
discrete. A compact discrete space is finite (`finite_of_compact_of_discrete`).

## The algebraically closed finiteness

`finite_of_isAlgClosed`: under the hypotheses at the top of this page,
`S.X.left` is finite. `exists_isClosed_isOpen_singleton` supplies the point.
`S.X.hom` is locally of finite type and `S.X.left` is affine, because
`s ≫ d` is a closed immersion into the affine `G.X.left`. So
`finite_of_isOpen_singleton` applies.

The finiteness concerns only the underlying space of `S`. No reducedness of `S`
is assumed: the reduced subgroup is used only to locate the point.
