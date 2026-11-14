# Statement: intersections with maximal tori, parabolic and Borel subgroups

Worker 75.

`Langlands.GroupScheme.NormalSubgroupIntersectionStatement.{u} : Prop` is a
statement-only, `Prop`-valued definition. This module does not prove it, and it adds no
other definitions, theorems or axioms. It imports
[`Reductive.QuasiSplit`](../Reductive/QuasiSplit.md), which provides
`IsGeometricBorelSubgroup i`: `IsBorelSubgroup i` holds, and the base change of `i` to the
algebraic closure `k̄` of `k` also satisfies `IsBorelSubgroup`.

Through this import it also uses:

- `IsBorelSubgroup` and `IsParabolicSubgroup` from
  [`Absolute.Borel`](../Absolute/Borel.md). `IsBorelSubgroup i` means that `i` is a
  closed subgroup with smooth, connected, solvable source, maximal among such closed
  subgroups defined over the base field. `IsParabolicSubgroup i` means that `i` is a
  closed subgroup with smooth source, and that some Borel subgroup of `G_{k̄}` factors
  through the base change `i_{k̄}`.
- `IsMaximalTorus` from [`Torus.Maximal`](../Torus/Maximal.md): `i : T ⟶ G` from a
  commutative group scheme with `IsTorus T` (from [`Torus.Lattice`](../Torus/Lattice.md):
  `T` becomes a split torus over some field extension) is a closed subgroup, and every
  factorization `i = f ≫ i'` through a closed torus `i' : T' ⟶ G` has `f` an
  isomorphism.
- `IsClosedSubgroup` from [`Reductive.Basic`](../Reductive/Basic.md): the underlying
  morphism of schemes is a closed immersion.
- `SubgroupFunctor.range`, `⊓`, `IsNormalizedBy` and `IsNormal` from
  [`SubgroupFunctor`](../SubgroupFunctor.md). For a homomorphism `n : N ⟶ G`,
  `(SubgroupFunctor.range n).carrier T` is the set of points `y ≫ n.hom.hom` with
  `y : T ⟶ N.X`, for every test scheme `T`. `F ⊓ F'` is the pointwise intersection.
  `F.IsNormalizedBy F'` means that `g * x * g⁻¹ ∈ F(T)` for all `g ∈ F'(T)`, `x ∈ F(T)`
  and every test scheme `T`. `F.IsNormal` is `F.IsNormalizedBy ⊤`. Equality of subgroup
  functors is equality on every test scheme.

All group schemes are over `Spec k` and in universe `u`.

## Statement

Let `k : Type u` be a field and `G` a group scheme over `Spec k` with `Smooth G.X.hom`,
`IsAffineHom G.X.hom` and `ConnectedSpace G.X.left`. Then the following two clauses hold.

1. **Maximal tori meet normalized subgroups in maximal tori.** Let `t : T ⟶ G` satisfy
   `IsMaximalTorus t`. Let `n : N ⟶ G` satisfy `IsClosedSubgroup n`, `Smooth N.X.hom`
   and `ConnectedSpace N.X.left`, with
   `(SubgroupFunctor.range n).IsNormalizedBy (SubgroupFunctor.range t)`. Then there are
   a commutative group scheme `C` and `c : C ⟶ N` with `IsMaximalTorus c` and
   `SubgroupFunctor.range (c ≫ n) = SubgroupFunctor.range n ⊓ SubgroupFunctor.range t`.

2. **Normal subgroups meet parabolic and Borel subgroups well.** Let `h : H ⟶ G`
   satisfy `IsClosedSubgroup h`, `Smooth H.X.hom`, `ConnectedSpace H.X.left` and
   `(SubgroupFunctor.range h).IsNormal`. Then:
   1. for every `p : P ⟶ G` with `IsParabolicSubgroup p` there is `q : Q ⟶ H` with
      `IsParabolicSubgroup q`, `ConnectedSpace Q.X.left` and
      `SubgroupFunctor.range (q ≫ h) = SubgroupFunctor.range h ⊓ SubgroupFunctor.range p`;
   2. for every `b : B ⟶ G` with `IsGeometricBorelSubgroup b` there is `c : C ⟶ H` with
      `IsGeometricBorelSubgroup c` and
      `SubgroupFunctor.range (c ≫ h) = SubgroupFunctor.range h ⊓ SubgroupFunctor.range b`.

## Source

Brian Conrad, *Reductive group schemes*, in *Autour des schémas en groupes* I, Panoramas
et Synthèses 42–43, SMF, 2014. It is registered as `conrad-2014-reductive-group-schemes`,
file `Conrad--Reductive group schemes (SGA3 notes)--2014.pdf` (SHA-256
`1a63a17e4ccb7e23263d65f05d93a6651262861e978e9eb0c1c53a01fd59140a`). Page numbers are
the printed page numbers.

- Exercise 5.5.1, p.182: "Let G be a smooth connected affine group over a field k.
  (i) For a maximal k-torus T in G (see Remark A.1.2) and a smooth connected
  k-subgroup N in G that is normalized by T, prove that T ∩ N is a maximal k-torus in N
  (e.g., smooth and connected!). Show by example that S ∩ N can be disconnected for a
  non-maximal k-torus S. […] (ii) Let H be a smooth connected normal k-subgroup of G,
  and P a parabolic k-subgroup. Prove (P_k̄ ∩ H_k̄)⁰_red is a parabolic subgroup of
  H_k̄, and use Theorem 1.1.9 (applied to H) to prove P ∩ H is connected (hint: work
  over k̄). (iii) For H as in (ii), by using that Q = N_H(Q) scheme-theoretically for
  parabolic Q in H (Corollary 5.2.8), prove P ∩ H in (ii) is smooth and therefore
  parabolic in H. […] In particular, prove that the scheme-theoretic intersection
  B ∩ H is a Borel k-subgroup of H for all Borel k-subgroups B of G." The omitted
  passages are hints.
- Remark A.1.2, p.267: over a field `k`, a `k`-torus of `G` not contained in a strictly
  larger `k`-torus stays maximal over every extension field, so "maximal `k`-torus" has
  only one meaning.

Conrad leaves the exercise to the reader; the notes contain no proof of it.

## Derivation from the source

- **Subgroups.** A `k`-subgroup of the affine group `G` is a closed subgroup scheme,
  encoded as a homomorphism with `IsClosedSubgroup`. "Smooth connected" is
  `Smooth` of the structure morphism together with `ConnectedSpace` of the underlying
  space. "Normal" for `H` is normality of `SubgroupFunctor.range h` on every test scheme.
  "Normalized by `T`" is `IsNormalizedBy` with respect to the range of `t`, again on every
  test scheme.
- **Maximal `k`-tori.** Conrad's maximal `k`-torus is maximal among `k`-tori of `G`
  under containment. `IsMaximalTorus` encodes exactly this maximality over `k`, and by
  Remark A.1.2 it agrees with geometric maximality.
- **Scheme-theoretic intersections.** For closed subgroups `h : H ⟶ G` and
  `p : P ⟶ G`, a `T`-point of `G` lies in `range h ⊓ range p` exactly when it factors
  through both `H` and `P`. These are the `T`-points of the fibre product `P ×_G H`,
  which is the scheme-theoretic intersection `P ∩ H`. In each conclusion the supplied
  subgroup, such as `q : Q ⟶ H`, is a closed subgroup of `H` (this is part of
  `IsMaximalTorus`, `IsParabolicSubgroup` and `IsGeometricBorelSubgroup`), so `q ≫ h`
  is a closed immersion. The range equation then says that `Q`, embedded in `G` through
  `q ≫ h`, has the same functor of points as `P ∩ H`; by Yoneda it is isomorphic to the
  scheme-theoretic intersection over `G`. Properties of `Q`, such as smoothness, are
  therefore properties of the scheme-theoretic intersection, as the exercise requires.
  This identification is explanation only; the Lean statement asserts the range
  equation.
- **Clause 1** is Exercise 5.5.1(i). `IsMaximalTorus c` includes `IsTorus C`, and a
  torus is smooth and connected, so the clause includes the smoothness and
  connectedness of `T ∩ N` that Conrad stresses.
- **Clause 2.1** combines (ii) and (iii). Exercise 5.5.1(iii) concludes that `P ∩ H` is
  smooth and hence a parabolic `k`-subgroup of `H`; (ii) shows that it is connected.
  `IsParabolicSubgroup q` contains smoothness and the closed-subgroup property, and
  `ConnectedSpace Q.X.left` is connectedness.
- **Borel `k`-subgroups (clause 2.2).** Over a field that need not be algebraically
  closed, Conrad's Borel `k`-subgroup of `G` is a `k`-subgroup whose base change to `k̄`
  is a Borel subgroup of `G_k̄`. The Library's `IsBorelSubgroup` alone only asks for
  maximality among smooth connected solvable `k`-subgroups, which is weaker over
  non-closed fields (an anisotropic maximal torus of the real group `SO(3)` is an
  example). The statement therefore uses `IsGeometricBorelSubgroup` for both `b` and
  `c`; this is also the reading recorded in
  [`RelativeLevi.Borel`](../RelativeLevi/Borel.md). Its first conjunct follows from the
  second, since a larger smooth connected solvable `k`-subgroup would give a larger
  one over `k̄`.

## Scope

The proposition does not state:

- the example in (i) of a non-maximal `k`-torus `S` with `S ∩ N` disconnected;
- the intermediate claim in (ii) that `(P_k̄ ∩ H_k̄)⁰_red` is a parabolic subgroup of
  `H_k̄`, which is a step towards clause 2.1;
- any of the hints, such as the normality of `(P ∩ H)⁰_red` in `P` when `k = k̄`.

## Relation to the Library

- `ParabolicIntersectionGeometryStatement` in
  [`Absolute.ParabolicIntersectionGeometryStatement`](../Absolute/ParabolicIntersectionGeometryStatement.md)
  concerns the intersection of two parabolic subgroups of a connected reductive group,
  not the intersection with a normal subgroup.
- `MaximalRankRadicalTorusIntersectionStatement` in
  [`Absolute.MaximalRankRadicalTorusIntersectionStatement`](../Absolute/MaximalRankRadicalTorusIntersectionStatement.md)
  uses the same range encoding of intersections, over an algebraically closed field.
- `RelativeParabolicNormalizerStatement` in
  [`RelativeParabolicNormalizerStatement`](../RelativeParabolicNormalizerStatement.md)
  states Corollary 5.2.8, which the hint to (iii) uses.

This module proves none of these relations.
