# Relative roots as restrictions of absolute roots: statement

Worker 3483.

`Langlands.GroupScheme.RelativeRootAbsoluteRestrictionStatement.{u}` is a
proposition definition. This module does not prove it.

## The statement

Let `k` and `K` be fields in the universe `u`, with a `k`-algebra structure on
`K`, and write `b = algebraBaseMap k K : Spec K ⟶ Spec k`. Let `G` be a group
scheme over `Spec k` with `IsConnectedReductive G`. Let `S` be a commutative
group scheme over `Spec k` and `i : S.toGrp ⟶ G` a maximal split torus,
`IsMaximalSplitTorus i`. Let `T` be a commutative group scheme over `Spec k`,
`j : T.toGrp ⟶ G` a maximal torus, `IsMaximalTorus j`, and `f : S ⟶ T` a
homomorphism with `CommGroupScheme.groupHom f ≫ j = i`; so `T` contains `S`.
Assume that `T` splits over `K`:
`IsSplitTorus ((GroupScheme.baseChange b).obj T.toGrp)`.

Write `j_K = (GroupScheme.baseChange b).map j` and
`f_K = (CommGroupScheme.baseChange b).map f`. The statement asserts that, for
every character `α` of `S`,

`α ∈ relativeRoots i ↔ α ≠ 0 ∧ ∃ β ∈ roots j_K, f_K ≫ β = characterLattice.baseChange b S α`.

In words: the relative roots of `(G, S)` are exactly the nonzero characters of
`S` whose base change to `K` is the restriction to `S_K` of a root of
`(G_K, T_K)`. Here `f_K ≫ β` is the restriction of the character `β` of `T_K`
along `S_K ⟶ T_K`.

The two `haveI` lines inside the definition only supply the instances
`IsAffineHom G.X.hom` (from `IsConnectedReductive G`) and
`IsAffineHom G_K.X.hom` (the base change of an affine morphism), which the
Library's `roots` and `relativeRoots` require. They add no hypothesis.

`relativeRoots i` is by definition `roots i`, the nonzero characters of `S`
with a nonzero weight space in the Lie algebra of `G` (`Rational/RelativeRoots`,
`Torus/Weights`). The roots of `j_K` are computed for the split torus `T_K`;
for the non-split `T` itself, `roots j` would only see the characters of `T`
defined over `k`, which is why the statement passes to `K`.

## Source

J. S. Milne, *Algebraic Groups: The Theory of Group Schemes of Finite Type
over a Field* (2017), source ID `milne-2017-algebraic-groups`, 25.19, printed
p.549 (PDF p.565):

> 25.19. Let S be a maximal split [torus] in G. Let T be a maximal torus
> containing S, and let Φ be the set of roots of (G,T)_{k^s}. Then _kΦ is the
> set of nontrivial restrictions to S of elements of Φ (Exercise 25-1).

and footnote 2 to 25.13, printed p.548 (PDF p.564):

> With this terminology, the absolute roots of G are the roots of (G,T)_{k^s},
> where T is a maximal torus T of G containing S. The relative roots are
> sometimes called restricted roots because they are the restrictions to S of
> the absolute roots (Exercise 25-1).

Milne's §25.b assumes `G` reductive over `k` (opening of 25.b, printed
p.548), and 25.13 defines the relative roots `_kΦ(G, S)` as the characters `α`
of `S` with `g_α ≠ 0` and `α` nontrivial. Milne's reductive groups are
connected group varieties (6.46, printed p.135: "A connected group variety
over a field k is said to be reductive if G_{k^a} is reductive"), matching the
Library's `IsConnectedReductive`.

## Correspondence with the source

- `G`, `S`, `T` and the inclusion `S ⊂ T` are Milne's data: `IsConnectedReductive`,
  `IsMaximalSplitTorus i`, `IsMaximalTorus j` and `groupHom f ≫ j = i`.
- `_kΦ` is `relativeRoots i`, the published Library notion matching 25.13.
- Milne's `Φ` is the set of roots of `(G, T)_{k^s}`. The statement allows any
  extension `K` over which `T` splits and uses the roots of `j_K`. The
  separable closure is the case `K = SeparableClosure k`. There `T_K` is split,
  because every torus over `k` splits over a finite Galois extension (published
  `torusFiniteGaloisSplitting`, `Torus/FiniteGaloisSplittingProof`), and that
  extension embeds into `k^s`. The `IsSplitTorus` hypothesis keeps the
  statement independent of that fact; it is not proved here for `k^s`.
- "Nontrivial restrictions to `S`" becomes `α ≠ 0` together with
  `f_K ≫ β = α_K`. Over `K` the restriction lands in the characters of `S_K`;
  the base change of characters of the split torus `S` is injective, so the
  restriction determines `α`.

The statement allows `K` larger than `k^s`, for example algebraically closed or
transcendental over `k`. For such `K` it remains the same assertion about the
roots of `(G_K, T_K)`, which correspond to those over `k^s` because `T` is
already split there. The statement asserts nothing about root multiplicities or
the weight spaces themselves.

## Relation to other Library results

The published theorem `mem_roots_iff_exists_splittingField_restriction`
(`Rational/AbsoluteRootRestriction`) proves the same equivalence under weaker
hypotheses. It takes any split torus `S`, any commutative `M` split over `K`,
`f : S ⟶ M` and `j : M ⟶ G` with `G` affine and locally of finite type, and
no maximality. The present statement packages Milne's assertion as a closed
proposition with Milne's hypotheses. The published family-5 ledger
(`notes/group-schemes/ledger-family-5-rational.md`, row I1) records the
theorem as D and lists such a closed proposition as an open obligation. A
proof by specialization of that theorem has been checked privately; it will be
submitted to a proof task.
