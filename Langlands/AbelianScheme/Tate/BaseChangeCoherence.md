# Identity and composition of actual Tate base change

This module constructs the canonical identity and composition isomorphisms
for actual group-scheme pullback and proves coherence of the existing
point, torsion-level, integral Tate, and rational Tate comparisons. It uses
arbitrary morphisms `b : S' ⟶ S` and `c : S'' ⟶ S'` of schemes in one
universe. The Tate results require `G` to be commutative and allow any
predicate `P : ℕ → Prop` selecting the positive torsion orders.

## Provenance

This is derived infrastructure for the Tate modules of Harris–Taylor,
*The Geometry and Cohomology of Some Simple Shimura Varieties* (2001),
printed p.18 / PDF p.26, and their use in the pointed PEL problem,
Section III.1, printed p.91 / PDF p.99. Registered source:
`harris-taylor-2001-geometry-cohomology-simple-shimura`, SHA-256
`5be28164b61d6f6cc28dd9e6b990d669504f3470860b230ebbc97e3da10af56b`.
Those passages supply the intended Tate-module conventions and application;
the coherence equations here are derived from actual pullbacks, rather than
attributed to a theorem in those passages.

The implementation reuses Mathlib's `Over.pullbackId` and
`Over.pullbackComp`, which are conjugates of the identity and composition
comparisons for `Over.map` through the pullback adjunctions.
`Functor.mapGrpNatIso`, `Functor.mapGrpIdIso`, and
`Functor.mapGrpCompIso` lift these existing comparisons to group objects.
The Tate comparisons themselves are the constructions in
`Tate.IntegralBaseChange` and `Tate.RationalBaseChange`.

## Group schemes and points

In namespace `Langlands.GroupScheme`, `baseChangeIdIso G` has type
`(id_S)*G ≅ G`. The theorem `baseChangeIdIso_hom_left` identifies its
underlying scheme morphism with the first pullback projection.

`baseChangeCompIso b c G` has type `(c ≫ b)*G ≅ c*(b*G)`.
`baseChangeCompIso_inv_fst` states that its inverse followed by the
projection from the direct pullback to `G` equals the two successive
projections from the iterated pullback to `b*G` and then to `G`.
The proof unfolds the lifted natural isomorphisms and the adjunction
comparison and simplifies the pullback projection equations. Both
isomorphisms are available for group schemes without commutativity.

Write `β_b` for `baseChangePointsEquiv b`, so a point of `b*G` on a
test scheme over `S'` becomes a point of `G` on that test scheme viewed
over `S`. The theorem `baseChangePointsEquiv_id` says that `β_id`,
precomposed with the inverse component of `Over.mapId`, agrees with
postcomposition by `baseChangeIdIso.hom`.

For a point `x` of `c*(b*G)` on `T` over `S''`,
`baseChangePointsEquiv_base_comp` says that applying `β_c` and then
`β_b` agrees with this sequence: postcompose `x` with
`baseChangeCompIso.inv`, apply `β_(c ≫ b)`, and precompose with
`(Over.mapComp c b).inv.app T`. The final precomposition identifies the
direct and iterated structure morphisms on the test scheme. These maps
have the same underlying scheme, but the comparison in the over category
is retained explicitly. Both point proofs reduce equality to the
underlying scheme morphisms and use the projection formulas above.

## Torsion levels and Tate modules

In namespace `Langlands.GroupScheme.Tate`, `levelBaseChange_id` and
`levelBaseChange_base_comp` are exactly the preceding point equations
restricted to the actual torsion subgroups, in additive notation. They
use `levelMap` for the group isomorphisms and `levelRestrict` for the
test-scheme comparisons. Injectivity of the actual torsion subgroup's
inclusion in sections reduces each proof to the point equation.

`integralBaseChange_id` and `integralBaseChange_base_comp` state the
same equations on `Integral G T P`. They use `map` and `testRestrict`.
Equality of each coordinate, proved by the corresponding finite-level
result, proves equality in the actual inverse limit.

`rationalBaseChange_id` and `rationalBaseChange_base_comp` state the
same equations on `Rational G T P = ℚ ⊗[ℤ] Integral G T P`, using
`rationalMap` and `rationalTestRestrict`. Tensor induction reduces pure
tensors to the integral equations and handles sums by additivity.

Taking `P` constantly true gives full Tate coherence; taking
`P n := Nat.Coprime n m` gives coherence away from `m`. The same
statements apply to a bundled abelian scheme by taking `G = A.toGrp`.
All group-scheme comparisons and Tate maps in these statements are
constructed from the actual pullbacks and torsion points.

## Scope

No invertibility of torsion orders, finite étaleness, connectedness,
noetherianity, or geometric-point hypothesis is used. These are algebraic
identity and binary composition equations for the existing comparisons.
This module does not establish a separate pentagon or triangle theorem
for the group-scheme natural isomorphisms, nor coherence wrappers in the
rationalized abelian-scheme category or its endomorphism tensor algebras.
It makes no rational topology, fundamental-group, Weil-pairing, or
invariant-level base-change claim. Those remain separate obligations.
