# Smooth connected solvable groups as semidirect products with a maximal torus

`Langlands.GroupScheme.SolvableMaximalTorusSemidirectStatement.{u}` is a
proposition target, not a proof.

Let `k : Type u` be an algebraically closed field and let `H` be a smooth
connected affine group scheme over `Spec k` that is solvable
(`IsSolvableGroupScheme H`). Let `s : T ⟶ H` be a maximal torus
(`IsMaximalTorus s`, with `T` a commutative group scheme). Then there is a
homomorphism `u : U ⟶ H` such that:

- `u` is a closed subgroup (`IsClosedSubgroup u`);
- `U` is smooth, connected and unipotent (`IsUnipotent U`);
- the range subgroup functor of `u` is normal in `H` on every test scheme
  (`SubgroupFunctor.IsNormal`);
- every unipotent closed subgroup `w : W ⟶ H` is contained in `U`:
  `SubgroupFunctor.range w ≤ SubgroupFunctor.range u`, an inclusion on
  every test scheme;
- the multiplication morphism `subgroupMultiplication u s : U × T → H`,
  sending `(n, t)` to `n * t` on every test scheme, is an isomorphism of
  schemes over `Spec k`.

## Source

J. S. Milne, *Algebraic Groups* (2017), Theorem 16.33, printed pp.335–336
(zero-based PDF pages 350–351). For a smooth connected solvable algebraic
group `G` over a perfect field, parts (a)–(c) give a normal unipotent
subgroup `G_u` that contains all unipotent algebraic subgroups of `G`, is
smooth and connected, and has torus quotient `G/G_u`. Part (d): if `k` is
algebraically closed and `T` is a maximal torus in `G`, then
`G = G_u ⋊ T`. This statement is the first clause of (d). It omits the
second clause of (d) (conjugacy of subgroups of multiplicative type into
`T`) and the quotient clauses of (a) and (c).

Milne, Definition 2.33, printed p.50 (zero-based PDF page 65): `G = N ⋊ Q`
when `N` is normal in `G` and `(n, q) ↦ nq : N(R) × Q(R) → G(R)` is a
bijection for every `k`-algebra `R`.

## Encodings

- Milne's algebraic groups are group schemes of finite type over `k`.
  Here `H` is smooth (so locally of finite presentation) and affine (so
  quasi-compact), hence of finite type. `U` is closed in `H`, hence also
  affine and of finite type.
- Solvability is the existing Library predicate `IsSolvableGroupScheme`, as
  in `Langlands.GroupScheme.SolvableUnipotentPartStatement`. For a smooth
  connected group over an algebraically closed field it agrees with Milne's
  solvability by Milne Proposition 16.34, (c)⇔(d), printed p.336.
- Maximal tori are the existing `IsMaximalTorus`: a closed torus not
  properly contained in another closed torus.
- The subgroup `G_u` of (a)–(c) is pinned down by the containment clause:
  a normal unipotent subgroup containing every unipotent closed subgroup is
  the largest unipotent closed subgroup. The smoothness, connectedness and
  normality clauses are Milne's (a) and (c).
- Milne's bijection on `R`-points for all `k`-algebras `R` is a bijection of
  functors on affine schemes over `k`. All schemes involved are affine over
  `k`, so by the Yoneda lemma it is the same as the multiplication morphism
  `subgroupMultiplication u s` being an isomorphism of schemes over
  `Spec k`. The factor order `(n, t)` is Milne's. The reversed order is
  equivalent by `isIso_subgroupMultiplication_reverse_iff`.
- Normality is the existing all-test-scheme encoding
  `SubgroupFunctor.IsNormal`.

The official author errata snapshot
`milne-2017-algebraic-groups-errata-2026-11-02` was read. It has no
correction to Definition 2.33, Theorem 16.33 or Proposition 16.34.

## Use

This is an input for the proof of
`Langlands.GroupScheme.MaximalRankRadicalTorusIntersectionStatement`. There,
a point in the intersection of an ambient maximal torus with the solvable
radical is written as `n * t` with `t` in a maximal torus of the radical
inside the ambient torus, and `n` in the unipotent part.

Source: `milne-2017-algebraic-groups`, SHA256
`899b0f44f3c3ccfbaf5ed1cf9c180be7a8016b1c0e9709ca0c206304e5bd1cd0`.
