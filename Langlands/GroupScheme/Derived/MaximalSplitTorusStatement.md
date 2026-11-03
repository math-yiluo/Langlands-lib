# A maximal split torus of a derived subgroup inside an ambient maximal split torus

Authors: Worker 1464, Worker 1384.

This module defines the proposition
`Langlands.GroupScheme.DerivedMaximalSplitTorusStatement.{u}`. It contains no
proof and adds no axioms.

## The statement

The universe `u` and the field `k : Type u` are arbitrary. In particular, `k`
may be imperfect or have positive characteristic. The data are:

- actual group schemes `G` and `D` over `Spec k` with `IsConnectedReductive G`;
- a homomorphism `d : D ⟶ G` with `IsDerivedSubgroup d`;
- a commutative group scheme `S` and a homomorphism `i : S.toGrp ⟶ G` with
  `IsMaximalSplitTorus i`.

The conclusion supplies a commutative group scheme `S_D` and homomorphisms
`j : S_D.toGrp ⟶ D` and `e : S_D ⟶ S` with three properties:

1. `IsMaximalSplitTorus j`: `j` is a maximal split torus of `D`;
2. `IsClosedSubgroup (CommGroupScheme.groupHom e)`: the underlying group
   homomorphism of `e` is a closed immersion;
3. `j ≫ d = CommGroupScheme.groupHom e ≫ i`: the two composites into `G` are
   equal as actual homomorphisms.

No maximal split torus of `D` is assumed. The proposition does not identify
the chosen `S_D` with a particular intersection or with its reduced identity
component, and it asserts no uniqueness. It does not assert that `e` is
surjective, or that the whole of `S` lies in `D`. For instance, the diagonal
torus of `GL_n` has dimension `n`, while its intersection with
`D = SL_n` has dimension `n - 1`. The statement mentions no simply connected
cover, no cocharacters and no surjectivity on rational points.

## The predicates

- `IsConnectedReductive G`, from
  [`Reductive.Basic`](../Reductive/Basic.md), says that the structure
  morphism of `G` is smooth and affine, that the underlying space is
  connected, and that the base change of `G` to an algebraic closure of `k`
  has no nontrivial smooth connected unipotent normal closed subgroup.
- `IsDerivedSubgroup d`, from [`Derived.Basic`](Basic.md), says that `d` is a
  closed immersion and that its range functor equals `derivedSubgroup G` on
  every test scheme, including nonreduced ones. `derivedSubgroup G` is the
  intersection of the ranges of all closed subgroups of `G` that contain every
  commutator. The range of `d` contains every commutator, so `d` is itself
  such a closed subgroup. It is therefore the smallest closed subgroup of `G`
  containing all commutators. This is not a condition on `k`-points alone.
- `IsMaximalSplitTorus`, from
  [`Rational.SplitTorus`](../Rational/SplitTorus.md), applies to a
  homomorphism from a commutative group scheme `T`. It requires that `T.toGrp`
  satisfy `IsSplitTorus`, that the homomorphism be a closed immersion, and
  that it be maximal. `IsSplitTorus`, from [`Torus.Split`](../Torus/Split.md),
  means isomorphic over the base to `splitTorus` on a finite index type,
  that is, to some `GL_1^r`. Maximality means: whenever the homomorphism
  factors as `f ≫ i'` through another closed split subtorus `i'`, the map `f`
  is an isomorphism.

## Source

Brian Conrad, Ofer Gabber and Gopal Prasad, *Pseudo-reductive groups*,
second edition (2015), registered source
`conrad-gabber-prasad-2015-pseudo-reductive`, SHA-256
`1b77af44c90211db9a3efa50896a3722f4fd2df332b7ce2ec52202eb243e7f54`.
The locators below were checked against the PDF.

- The opening of Appendix C, printed p.581 / PDF p.607, sets the scope:
  "Let G be a smooth connected affine group over a field k". The field is
  arbitrary.
- Definition C.2.11, printed p.599 / PDF p.625: a quasi-reductive `k`-group
  is a smooth connected affine `k`-group `G` with `R_{us,k}(G)` trivial.
- The setup C.2.13 begins on printed p.599 / PDF p.625 and continues on
  printed p.600 / PDF p.626. It fixes a maximal `k`-split torus `S` of a
  smooth connected affine `k`-group `G`.
- Theorem C.2.15, printed p.603 / PDF p.629: "If G is quasi-reductive then:
  … S′ := (S ∩ D(G))⁰_red is a maximal k-split torus of D(G)".
- Step 1 of its proof, printed p.604 / PDF p.630, derives this by applying
  Remark C.2.12(2) to a maximal `k`-torus of `G` containing `S`.

Only this derived-torus assertion is used. The root datum, the almost direct
product with the central split torus and the remaining conclusions of the
theorem are not included. The remark just before the proof, printed p.604 /
PDF p.630, uses `G_a ⋊ GL_1` to show that, when `R_{us,k}(G) ≠ 1`, both
`(S ∩ D(G))⁰_red` and the maximal central split `k`-torus can be trivial even
if `S ≠ 1`. That example obstructs the almost-direct-product conclusion, not
the derived-torus assertion used here: in it `D(G) = G_a`, whose maximal
split torus is trivial. Quasi-reductivity enters here only because the
source states and proves C.2.15 under that hypothesis. No retained project
errata file for this source was present when checked.

## Translation

The proposition is a derived existential reformulation of the C.2.15
assertion for connected reductive groups. Each hypothesis and conclusion
corresponds to the source as follows.

**Scope.** `IsConnectedReductive G` includes smoothness, affineness and
connectedness. An affine morphism is quasi-compact, and smoothness gives
local finite presentation, so `G` is of finite type over `k`. Thus `G` is a
smooth connected affine `k`-group in the sense of Appendix C. No
separability, perfectness, characteristic or valued-field hypothesis is
added.

**Quasi-reductivity.** A connected reductive `G` is quasi-reductive. The
base change of `R_{u,k}(G)` to an algebraic closure is a smooth connected
unipotent normal closed subgroup of the base change of `G`. By
`IsConnectedReductive G` it is trivial. Hence `R_{u,k}(G) = 1`, and so its
split part `R_{us,k}(G)` is trivial too.

**The derived group.** The source writes `D(G)` for the derived group. J. S.
Milne, *Algebraic Groups* (2017), registered source
`milne-2017-algebraic-groups`, SHA-256
`899b0f44f3c3ccfbaf5ed1cf9c180be7a8016b1c0e9709ca0c206304e5bd1cd0`, defines
`DG` in Definition 6.16. Proposition 6.18 (printed p.129 / PDF p.145)
identifies `DG`, for affine or smooth `G`, with the algebraic subgroup
generated by the commutator map. Its proof describes this subgroup as the
smallest algebraic subgroup containing the commutators of `G(R)` for every
`k`-algebra `R`. Corollary 6.19(b), on the same page,
says that `DG` is smooth and connected when `G` is. The published
[`Derived.Basic`](Basic.md) explains that `derivedSubgroup` is a
reformulation of the description in Proposition 6.18. As explained under
the predicates, any `d` with `IsDerivedSubgroup d` is the smallest closed
subgroup containing all commutators. So the supplied `d` already represents
the source's `D(G)` as a closed subgroup of `G`.

**The ambient torus.** `IsMaximalSplitTorus i` says that `S` is a split
torus over `k` and `i` a closed immersion. For closed split subtori, the
factorization condition says that `i(S)` is contained in no strictly larger
`k`-split subtorus of `G`. This is the source's maximal `k`-split torus `S`.

**The witnesses.** The source's `S′` is a closed subgroup scheme of the
commutative `S`, so it is a commutative group scheme. Let `S_D := S′`, let
`e` be its inclusion into `S`, and let `j` be its inclusion into `D(G)`.
Both are closed immersions, which gives the second conclusion. Both
composites into `G` are the inclusion of `S′`, which gives the third.
The first conclusion is the source's assertion that `S′` is a maximal
`k`-split torus of `D(G)`, read through the same maximality translation as
for `S`. The Lean conclusion records only these inclusions, as actual
homomorphisms on all test schemes. It does not mention the intersection.

**Transport to the supplied inclusion.** Two inclusions satisfying
`IsDerivedSubgroup` are canonically isomorphic over `G`, by the uniqueness of
representations of a subgroup functor,
`SubgroupFunctor.IsRepresentedBy.isoOfIsRepresentedBy`. The published module
[`Derived.SplitTorusTransport`](SplitTorusTransport.md) (Worker 1464) packages
this as `IsDerivedSubgroup.iso` with the identity
`IsDerivedSubgroup.iso_hom_comp`. Its
`IsDerivedSubgroup.exists_maximalSplitTorus_factor_iff` proves that the
existential conclusion of this proposition holds for one such inclusion if
and only if it holds for another, with the same `S` and `i`. So quantifying
over every supplied `d` asks for no more than the source gives for its own
`D(G)`. The present module does not import that transport module.

## Consumer

This is the first existential layer of
`SimplyConnectedDerivedCoverSplitTorusStatement` in
[`SimplyConnected.DerivedCoverSplitTorusStatement`](../SimplyConnected/DerivedCoverSplitTorusStatement.md),
with the simply connected cover omitted. A proof of the present statement
would supply the derived torus required there. The covering-torus geometry
and the rational and real cocharacter arguments remain separate
obligations. This module proves none of those results.
