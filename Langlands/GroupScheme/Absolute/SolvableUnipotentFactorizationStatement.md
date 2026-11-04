# Rational unipotent-times-torus factorization of solvable groups

`Langlands.GroupScheme.SolvableUnipotentFactorizationStatement.{u}` is a
proposition target. It asserts no proof.

## Statement

Let `k : Type u` be an algebraically closed field and let `B` be a smooth,
affine group scheme over `Spec k` whose underlying space is connected
(`[Smooth B.X.hom] [IsAffineHom B.X.hom] [ConnectedSpace B.X.left]`). Assume
`IsSolvableGroupScheme B`. Let `T` be a commutative group scheme over
`Spec k` and let `t : T.toGrp ⟶ B` be a maximal torus (`IsMaximalTorus t`).
The maximal torus is supplied by the caller and is arbitrary. Then there
exist a group scheme `U` over `Spec k` and a homomorphism `a : U ⟶ B` such
that:

- `a` is a closed subgroup (`IsClosedSubgroup a`, a closed immersion);
- `U` is smooth, its underlying space is connected, and `U` is unipotent
  (`IsUnipotent U`);
- the range subgroup functor of `a` is normal on every test scheme over
  `Spec k` (`(SubgroupFunctor.range a).IsNormal`);
- every point `b ∈ B(k)` has a factorization `b = a(v) * t(s)` with
  `v ∈ U(k)` and `s ∈ T(k)`. In Lean this reads
  `(v ≫ a.hom.hom) * (s ≫ t.hom.hom) = b`.

Here `rationalPoints G` is the group of sections `Spec k ⟶ G` over
`Spec k`, with the group law of `G`. The product takes the unipotent
factor first, then the torus factor.

The subgroup `U` is existentially quantified after `t` is given. The
statement does not require `U` to be the same for different maximal tori.
It also does not require `U` to contain every unipotent subgroup. For that
property see `Langlands.GroupScheme.SolvableUnipotentPartStatement`.

## Source and correspondence

J. S. Milne, *Algebraic Groups* (2017), Theorem 16.33. The theorem starts on
printed p.335 (zero-based PDF page 350), and parts (a)–(d) are on printed
p.336 (zero-based PDF page 351). For a smooth connected solvable algebraic
group `G` over a perfect field:

- (a) gives a normal unipotent subgroup `G_u` with `G/G_u` of
  multiplicative type;
- (c) says `G_u` is smooth and connected;
- (d) says that when `k` is algebraically closed and `T` is a maximal torus
  in `G`, then `G = G_u ⋊ T`.

Milne's Definition 2.33 (printed p.50, zero-based PDF page 65) defines
`G = N ⋊ Q` to mean that `N` is normal and that `(n, q) ↦ nq` is a
bijection `N(R) × Q(R) → G(R)` for every `k`-algebra `R`. Taking `R = k`
gives the ordered factorization of `k`-points stated here, with `U = G_u`.
An algebraically closed field is perfect, so the theorem applies.

How the Lean hypotheses match Milne's:

- Milne's algebraic groups are group schemes of finite type over `k`. `B`
  is smooth, hence locally of finite presentation, and affine, hence
  quasi-compact. So `B` is of finite type. Closed subgroups of `B` are
  affine and of finite type as well.
- Algebraic subgroups in Milne's sense are closed subgroup schemes. This is
  what `IsClosedSubgroup` encodes for `a`, and what `IsMaximalTorus`
  requires of `t`.
- `IsMaximalTorus t` means that `T` is a torus (`IsTorus`: split after base
  change to some field extension, Milne 12.14), that `t` is a closed
  subgroup, and that `t` is maximal: whenever `t = f ≫ i'` for a closed
  torus `i' : T' ⟶ B`, `f` is an isomorphism. So `T` is not properly
  contained in a larger torus of `B`. This is the standard meaning of a
  maximal torus. Theorem 16.33(d) uses the term without further
  qualification.
- `IsUnipotent U` says that every nonzero finite-dimensional matrix
  representation of `U` has a nonzero fixed vector. This is Milne's
  definition of unipotence (6.45, restated on printed p.280). Milne notes
  there that it suffices to check finite-dimensional representations.
- Milne's normality is a condition on `R`-points for every `k`-algebra `R`.
  The Lean statement uses `SubgroupFunctor.IsNormal`, which is the same
  condition on points over every scheme over `Spec k`. A morphism factors
  through a closed subscheme if it does so locally on an affine open cover.
  So the two conditions agree.
- `IsSolvableGroupScheme B` says that the abstract group of points of the
  base change of `B` to `AlgebraicClosure k` is solvable. Since `k` is
  algebraically closed, `k → AlgebraicClosure k` is an isomorphism, so this
  is solvability of the abstract group `B(k)`. Milne's Proposition 16.34,
  (c)⇔(d), printed p.336, shows that for a smooth connected group over an
  algebraically closed field this is equivalent to Milne's solvability. The
  existing `SolvableUnipotentPartStatement` uses the same convention.

## What is omitted

This statement keeps only the existence of the factors on base points. It
does not assert:

- uniqueness of the factorization, or `U(k) ∩ T(k) = 1`;
- that multiplication `U × T → B` is an isomorphism of schemes, or
  surjectivity of points over every test scheme;
- that `B/U` is a torus isomorphic to `T`;
- part (b) of Theorem 16.33 (`G_u` contains all unipotent subgroups and
  commutes with base change), or the uniqueness clause of (c);
- the second clause of (d): conjugacy of subgroups of multiplicative type
  into `T` by elements of `G_u(k)`.

## Errata

The official author errata snapshot
`milne-2017-algebraic-groups-errata-2026-11-02` was read in full. Its
Chapter 16 entries concern p.324, p.330 and p.349 (16.65), and its
Chapter 2 entries concern p.48 and p.51. It has no correction to Theorem
16.33, Proposition 16.34 or Definition 2.33.

Source: `milne-2017-algebraic-groups`, SHA256
`899b0f44f3c3ccfbaf5ed1cf9c180be7a8016b1c0e9709ca0c206304e5bd1cd0`.

## Use

This target was requested as a prerequisite for the Borel normalizer proof
(task `de4ee66f-60ba-4f0f-8a3f-77cf0da95413`). It provides the
factorization of `B(k)` into a unipotent part and a maximal-torus part. The
present statement proves neither the factorization nor that theorem.
