# Statement: the centralizer of a multiplicative subgroup is open in its normalizer

Worker 75.

`Langlands.GroupScheme.MultiplicativeTypeCentralizerOpenStatement.{u} : Prop` is a
statement-only, `Prop`-valued definition. This module does not prove it, and it adds no
other definitions, theorems or axioms. It imports:

- [`Torus.MultiplicativeType`](MultiplicativeType.md), for the field-level predicate
  `IsMultiplicativeType`;
- [`Rational.TorusNormalizer`](../Rational/TorusNormalizer.md), for the normalizer and
  centralizer subgroup functors `SubgroupFunctor.normalizer` and
  `SubgroupFunctor.centralizer`.

`IsClosedSubgroup`, `SubgroupFunctor.range` and `SubgroupFunctor.IsRepresentedBy` come
through the imports of these two modules.

`GroupScheme S` is `Grp (Over S)`, and a morphism `i : H ⟶ G` in it is a homomorphism of
group schemes over `S`. Its underlying morphism of `S`-schemes is `i.hom.hom : H.X ⟶ G.X`,
and `i.hom.hom.left` is the underlying morphism of schemes. A point of `G` over a test
object `T : Over S` is a morphism `T ⟶ G.X` over `S`.

## Lean statement

```lean
def MultiplicativeTypeCentralizerOpenStatement : Prop :=
  ∀ (k : Type u) [Field k] (G H : GroupScheme (Spec (CommRingCat.of k))) (i : H ⟶ G),
    LocallyOfFiniteType G.X.hom → QuasiCompact G.X.hom →
    IsMultiplicativeType H → IsClosedSubgroup i →
      ∀ (N C : GroupScheme (Spec (CommRingCat.of k))) (n : N ⟶ G) (c : C ⟶ G) (f : C ⟶ N),
        (SubgroupFunctor.range i).normalizer.IsRepresentedBy n →
        (SubgroupFunctor.range i).centralizer.IsRepresentedBy c →
        f ≫ n = c → IsOpenImmersion f.hom.hom.left
```

## Predicates used

- `IsMultiplicativeType H` (field level): there are a field `K : Type u`, an algebra
  `k → K`, a finitely generated abelian group `Λ : Type u` and an isomorphism of group
  schemes over `Spec K` from the base change `H_K` onto
  `Diagonalizable.groupScheme (CommRingCat.of K) Λ`, the diagonalizable group
  `D_K(Λ) = Spec K[Λ]`. This is Milne's Definition 12.17 for algebraic groups (groups of
  finite type), as documented in [`Torus.MultiplicativeType`](MultiplicativeType.md).
- `IsClosedSubgroup i`: the underlying morphism of schemes `i.hom.hom.left` is a closed
  immersion.
- `SubgroupFunctor.range i`: the subgroup functor of `G` whose `T`-points are the
  `T`-points of `G` that factor through `i`.
- `F.normalizer`: the subgroup functor of `G` whose `U`-points are the points `g` such that
  for every `a : V ⟶ U`, conjugation by `a ≫ g` and by its inverse maps the `V`-points of
  `F` into the `V`-points of `F`.
- `F.centralizer`: the subgroup functor of `G` whose `U`-points are the points `g` such that
  for every `a : V ⟶ U`, the point `a ≫ g` commutes with every `V`-point of `F`.
- `F.IsRepresentedBy n` for `n : N ⟶ G`: the morphism `n.hom.hom` is a monomorphism and
  `SubgroupFunctor.range n = F`, so the points of `N` over every test object are exactly the
  points of `F`.
- `IsOpenImmersion f.hom.hom.left`: the underlying morphism of schemes of `f` is an open
  immersion.

## Statement and quantifiers

The proposition quantifies over a field `k : Type u`, group schemes `G`, `H` over `Spec k`
and a homomorphism `i : H ⟶ G` such that the structure morphism of `G` is locally of finite
type and quasi-compact, `H` is of multiplicative type, and `i` is a closed immersion. For all
group schemes `N`, `C` over `Spec k` and homomorphisms `n : N ⟶ G`, `c : C ⟶ G` and
`f : C ⟶ N` such that `n` represents the normalizer of `range i`, `c` represents its
centralizer, and `f ≫ n = c`, it concludes that `f` is an open immersion.

The representatives `n` and `c` are hypotheses: the statement does not assert that they
exist. Since `n.hom.hom` is a monomorphism, `f` is determined by `n` and `c`. The group `G` is
not assumed to be affine, smooth or connected, and `H` is not assumed to be smooth or
connected.

## Source

James S. Milne, *Algebraic Groups: The theory of group schemes of finite type over a field*
(Cambridge University Press, 2017), source ID `milne-2017-algebraic-groups`, file
`Milne--Algebraic groups, the theory of group schemes of finite type over a field
(book)--2017.pdf`. Page numbers are printed page numbers; the PDF page is the printed page
plus 16.

- Corollary 12.40, p.244: "Let H be a subgroup of multiplicative type of an algebraic group
  G. Then N_G(H)° = C_G(H)°, i.e., C_G(H) is an open subgroup of N_G(H)." This is the
  statement, in its second form.
- Milne's proof applies the rigidity theorem, Theorem 12.36, p.243, to the family
  `N_G(H)° × H → H`, `(g, h) ↦ g h g⁻¹`, which gives `N_G(H)° ⊂ C_G(H)`. This is
  explanation only.
- Proposition 1.83, p.31, and Proposition 1.92, p.33, define `N_G(H)` and `C_G(H)` for an
  algebraic subgroup `H` of an algebraic group `G`. They are the algebraic subgroups of `G`
  representing the functors
  `R ↦ {g ∈ G(R) | g H_R g⁻¹ = H_R}` and
  `R ↦ {g ∈ G(R) | g centralizes H(R') in G(R') for all R-algebras R'}`.

## Derivation from the source

- **Algebraic group.** Milne's algebraic groups are group schemes of finite type over `k`
  (Definition 1.1, p.6). The statement encodes "of finite type" as
  `LocallyOfFiniteType G.X.hom` together with `QuasiCompact G.X.hom`.
- **Subgroup of multiplicative type.** In Milne a subgroup of an algebraic group is an
  algebraic subgroup, that is, a closed group subscheme. The statement takes a closed
  immersion `i : H ⟶ G` (`IsClosedSubgroup i`) with `IsMultiplicativeType H` (Milne,
  Definition 12.17, p.236).
- **Normalizer and centralizer.** Milne's `N_G(H)` and `C_G(H)` are the algebraic subgroups
  representing the functors of Propositions 1.83 and 1.92. The Library functors
  `(SubgroupFunctor.range i).normalizer` and `(SubgroupFunctor.range i).centralizer` are
  these functors, extended from `k`-algebras to all test schemes over `Spec k` and tested
  after every refinement. For `N_G(H)`, the condition `g H_R g⁻¹ = H_R` is the condition
  that conjugation by `g` and by `g⁻¹` preserves the points of `H` over every `R`-algebra.
  The statement takes arbitrary representatives `n` and `c` (monomorphisms with exactly
  these points) rather than a chosen construction. The inclusion `C_G(H) ⊂ N_G(H)` is the
  homomorphism `f` with `f ≫ n = c`.
- **Open subgroup.** "`C_G(H)` is an open subgroup of `N_G(H)`" is
  `IsOpenImmersion f.hom.hom.left`. This is equivalent to Milne's first form
  `N_G(H)° = C_G(H)°`: an open subgroup contains the identity component, and if `C_G(H)`
  contains `N_G(H)°`, then `C_G(H)` is a union of cosets of the open subgroup `N_G(H)°`.
- **Existence of representatives.** Milne's Propositions 1.83 and 1.92 give closed
  representatives for every algebraic group `G`. The statement does not include this
  existence claim. For affine `G` it is the Library theorem
  `hasClosedRepresentative_normalizer_centralizer_range`
  ([`NormalizerRepresentability`](../NormalizerRepresentability.md)), so the statement has
  content at least for affine algebraic groups.
- **Universes.** The field `k`, the splitting field and the character group in
  `IsMultiplicativeType` all live in the universe `u`.

## Related Library results

- `hasClosedRepresentative_normalizer_centralizer_range`
  ([`NormalizerRepresentability`](../NormalizerRepresentability.md)) proves that the
  normalizer and centralizer of a closed subgroup of an affine group scheme over a field
  have closed representatives.
- [`Torus.WeylImageFiniteStatement`](WeylImageFiniteStatement.md) states finiteness of the
  normalizer image of a closed split torus in an affine algebraic group, and cites
  Corollary 12.40 in its derivation. It does not state 12.40.
- [`Torus.HomFamilyRigidity`](HomFamilyRigidity.md) proves the split-torus case of the
  rigidity theorem 12.36.
