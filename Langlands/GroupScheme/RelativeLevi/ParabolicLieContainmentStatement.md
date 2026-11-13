# Statement: containment of Lie algebras at a point spreads to a Zariski neighbourhood

Worker 75.

`Langlands.GroupScheme.RelativeParabolicLieContainmentStatement.{u} : Prop` is a
statement-only, `Prop`-valued definition. This module does not prove it, and it adds no
other definitions, theorems or axioms. It imports [`RelativeLevi.Basic`](Basic.md), for
`IsRelativeParabolicSubgroup` and `RelativeLevi.residueFiberHom`,
[`Torus.FieldPointMaximality`](../Torus/FieldPointMaximality.md), for
`IsFibrewiseMaximalTorus`, [`Torus.Relative`](../Torus/Relative.md), for
`RelativeTorus.IsTorus`, and [`Lie.SubgroupTangent`](../Lie/SubgroupTangent.md), for the
tangent submodule `SubgroupFunctor.lie`.

## Statement and quantifiers

The proposition quantifies over:

- every scheme `S : Scheme.{u}`;
- group schemes `G P Q : GroupScheme S` and homomorphisms `i : P ⟶ G`, `j : Q ⟶ G`;
- a commutative group scheme `T : CommGroupScheme S` and a homomorphism
  `t : T.toGrp ⟶ G`;
- a point `s : S`.

It has nine hypotheses:

1. `hG : IsReductive G` ([`Reductive.Basic`](../Reductive/Basic.md)): `G` is smooth and
   affine over `S`, and its geometric fibres are connected reductive groups.
2. `IsRelativeParabolicSubgroup i` ([`RelativeLevi.Basic`](Basic.md)): `P` is smooth and
   affine over `S`, `i` is a monomorphism of `S`-schemes, and every residue fibre of `i`
   satisfies the field predicate `IsParabolicSubgroup`.
3. `IsRelativeParabolicSubgroup j`, the same for `j`.
4. `RelativeTorus.IsTorus T.toGrp`: there is an étale cover of `S` over each member of
   which `T` becomes a split torus.
5. `IsClosedSubgroup t`: the underlying morphism of schemes `T ⟶ G` is a closed
   immersion.
6. `IsFibrewiseMaximalTorus t`: for every point `s'` of `S`, the residue fibre of `t` over
   `κ(s')` satisfies the field predicate `IsMaximalTorus` in `G_{s'}`.
7. `SubgroupFunctor.range t ≤ SubgroupFunctor.range i`: on every test scheme, every point
   of `G` that factors through `t` factors through `i`, so `T ⊆ P`.
8. `SubgroupFunctor.range t ≤ SubgroupFunctor.range j`, so `T ⊆ Q`.
9. **Lie algebra containment at `s`.** Write `G_s` for the base change of `G` along
   `S.fromSpecResidueField s : Spec κ(s) ⟶ S`, and `i_s`, `j_s` for
   `RelativeLevi.residueFiberHom i s` and `RelativeLevi.residueFiberHom j s`. Then

       (SubgroupFunctor.range j_s).lie κ(s) ≤ (SubgroupFunctor.range i_s).lie κ(s)

   as `κ(s)`-submodules of `lieKernel G_s κ(s)`, the kernel of reduction
   `G_s(κ(s)[ε]) → G_s(κ(s))` ([`Lie.DualNumberKernel`](../Lie/DualNumberKernel.md)).
   For a subgroup functor `F` of `G_s`, `F.lie κ(s)` consists of the elements of this
   kernel that lie in `F` ([`Lie.SubgroupTangent`](../Lie/SubgroupTangent.md)).

Hypothesis 9 is elaborated with two local instances. `hG.isAffineHom` makes
`G.X.hom` affine, and the instance that `G_s ⟶ Spec κ(s)` is affine is obtained from it
by `inferInstanceAs`, since that morphism is the second projection of the pullback of
`G.X.hom` along `S.fromSpecResidueField s`. `SubgroupFunctor.lie` needs this instance.

The conclusion is: there is an open subscheme `V : S.Opens` with `s ∈ V` such that

    SubgroupFunctor.range ((GroupScheme.baseChange V.ι).map j)
      ≤ SubgroupFunctor.range ((GroupScheme.baseChange V.ι).map i),

where `V.ι : V ⟶ S` is the open immersion. On every scheme over `V`, every point of
`G_V` that factors through `Q_V` factors through `P_V`; that is, `Q_V ⊆ P_V`.

## Source

Brian Conrad, *Reductive group schemes*, in *Autour des schémas en groupes* I,
Panoramas et Synthèses 42–43, SMF, 2014. It is registered as
`conrad-2014-reductive-group-schemes`, file
`Conrad--Reductive group schemes (SGA3 notes)--2014.pdf` (SHA-256
`1a63a17e4ccb7e23263d65f05d93a6651262861e978e9eb0c1c53a01fd59140a`). Page numbers are
the one-based PDF pages, which agree with the printed page numbers.

- Corollary 5.2.7, p.155: "Let G → S be a reductive group, s ∈ S a point, and P, Q ⊂ G
  parabolic subgroups. [...] 2. Assume P and Q contain a common maximal torus T of G. If
  Lie(Q_s) ⊂ Lie(P_s) inside g_s then Q_V ⊂ P_V for some Zariski-open neighborhood V of
  s in S."
- Definition 5.2.1, p.151 (parabolic subgroups), and Definition 3.1.1, p.81 (reductive
  group schemes and `S`-tori: "An S-torus is an S-group T → S of multiplicative type with
  smooth connected fibers").
- Definition 3.2.1, p.91: "A maximal torus in a smooth S-affine group scheme G → S is a
  torus T ⊂ G such that for each geometric point s̄ of S the fiber T_s̄ is not contained
  in any strictly larger torus in G_s̄."
- Remark A.1.2, p.267: over a field `k`, maximality of a `k`-torus in the geometric
  sense of Definition 3.2.1 is the same as maximality among `k`-tori.
- Proposition B.3.4, pp.290–291: a group of multiplicative type is diagonalizable
  étale-locally on `S`.
- Lemma B.1.3, p.281: a monic homomorphism from a group of multiplicative type to an
  `S`-affine `S`-group of finite presentation is a closed immersion.

## Derivation from the source

The proposition is the first assertion of Corollary 5.2.7(2), with its terms translated
as follows.

- **"A common maximal torus T of G".** `T` is given abstractly with `t : T ⟶ G`.
  Hypotheses 4–6 say that `t` is a maximal torus of `G`, as in the published
  [`TorusLeviStatement`](TorusLeviStatement.md): `RelativeTorus.IsTorus` is étale-local
  splitting, which by Proposition B.3.4 is equivalent to being an `S`-torus;
  closedness adds nothing by Lemma B.1.3; and maximality on residue fibres agrees with
  maximality on geometric fibres by Remark A.1.2. "P and Q contain T" is hypotheses 7
  and 8, inclusion of images as subgroup functors of `G`.
- **"Lie(Q_s) ⊂ Lie(P_s) inside g_s".** Here `s` stands for the fibre over `κ(s)` and
  `g_s = Lie(G_s)`. The Lie algebra of `G_s` is the kernel of reduction
  `G_s(κ(s)[ε]) → G_s(κ(s))`, and `Lie(P_s)` sits inside it as the dual-number points of
  `P_s` that reduce to the identity. Because `i_s` is a monomorphism, these are exactly
  the elements of the kernel lying in the image of `i_s`, which is
  `(SubgroupFunctor.range i_s).lie κ(s)`. The published theorem
  `SubgroupFunctor.lie_eq_range` identifies this submodule with the range of the linear
  map induced by `i_s` on identity kernels. Hypothesis 9 is the stated containment.
- **"Q_V ⊂ P_V for some Zariski-open neighborhood V of s".** `V` is an open subscheme of
  `S` containing `s`, and the containment of subgroups of `G_V` is inclusion of images as
  subgroup functors, the convention used throughout the relative Levi statements of the
  Library. Because `i` and `j` are monomorphisms, this is the containment of subgroups
  `Q_V ⊆ P_V` of `G_V`.

## Scope

All objects are in universe `u`. The base `S` is an arbitrary scheme: it need not be
affine, Noetherian, reduced or connected. `T` need not be split over `S`, and no
cocharacter or splitting is given. `P` and `Q` are not assumed closed in `G`.

## Not stated

- The second sentence of Corollary 5.2.7(2), "if Lie(P_s) = Lie(Q_s) inside g_s then P
  and Q coincide over a Zariski-open neighborhood of s in S", is not stated separately.
- Corollary 5.2.7(1), étale-local conjugacy of parabolic subgroups conjugate at a point,
  is the published [`ParabolicEtaleConjugacyStatement`](ParabolicEtaleConjugacyStatement.md).

This module proves none of these assertions.
