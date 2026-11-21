# Statement: extensions of connected groups of multiplicative type

Worker 75.

`Langlands.GroupScheme.MultiplicativeTypeConnectedExtensionStatement.{u} : Prop` is a
statement-only, `Prop`-valued definition. This module does not prove it, and it adds no other
definitions, theorems or axioms. It imports:

- [`Torus.MultiplicativeType`](MultiplicativeType.md), for the field-level predicate
  `IsMultiplicativeType`.
- [`Rational.RootSubgroupStructureStatement`](../Rational/RootSubgroupStructureStatement.md),
  for `RelativeRoot.IsFppfQuotient` and, through its imports, `IsClosedSubgroup` and the
  group-scheme vocabulary over a field.

## Lean statement

```lean
def MultiplicativeTypeConnectedExtensionStatement : Prop :=
  ∀ (k : Type u) [Field k] (N G Q : GroupScheme (Spec (CommRingCat.of k)))
    [LocallyOfFiniteType G.X.hom] [IsAffineHom G.X.hom] (i : N ⟶ G) (q : G ⟶ Q),
    IsClosedSubgroup i → RelativeRoot.IsFppfQuotient (SubgroupFunctor.range i) q →
    IsMultiplicativeType N → IsMultiplicativeType Q → ConnectedSpace Q.X.left →
      IsMultiplicativeType G
```

## Objects and predicates used

- **Group schemes.** `GroupScheme S` is `Grp (Over S)`. For `G : GroupScheme S`, `G.X.left`
  is the underlying scheme and `G.X.hom` its structure morphism.
- `LocallyOfFiniteType`, `IsAffineHom`, `ConnectedSpace`: as in Mathlib.
- `IsClosedSubgroup i` ([`Reductive.Basic`](../Reductive/Basic.md)): the underlying morphism of
  schemes of `i` is a closed immersion.
- `RelativeRoot.IsFppfQuotient F q`
  ([`Rational.RootSubgroupStructureStatement`](../Rational/RootSubgroupStructureStatement.md)):
  the underlying morphism of `q` is flat, surjective and locally of finite presentation, and
  the kernel of `q` has image `F` on every test scheme.
- `IsMultiplicativeType H` ([`Torus.MultiplicativeType`](MultiplicativeType.md)): after base
  change to some field extension `K` of `k`, `H` becomes isomorphic to the diagonalizable group
  `D(Λ)` of a finitely generated abelian group `Λ`.

## Statement and quantifiers

For every field `k : Type u`, all group schemes `N`, `G`, `Q` over `Spec k` with `G` of finite
type and affine, every closed subgroup `i : N ⟶ G` and every fppf quotient map `q : G ⟶ Q`
whose kernel is `N` (so that `e → N → G → Q → e` is exact): if `N` and `Q` are of
multiplicative type and `Q` is connected, then `G` is of multiplicative type.

## Source

James S. Milne, *Algebraic Groups: The theory of group schemes of finite type over a field*
(Cambridge University Press, 2017), source ID `milne-2017-algebraic-groups`, file
`Milne--Algebraic groups, the theory of group schemes of finite type over a field
(book)--2017.pdf`. Page numbers are printed page numbers; the PDF page is the printed page
plus 16. The 2022 corrected reprint has source ID `milne-2022-algebraic-groups`; its PDF page
is the printed page plus 11.

- Theorem 15.39, p.322 (2017): "Every extension of a connected algebraic group of
  multiplicative type by an algebraic group of multiplicative type is of multiplicative type."
  The 2022 reprint (p.322) reads "by a group of multiplicative type".
- Chapter 15 opening, p.302 (2017): "Recall that all algebraic groups are affine over the base
  field k." The 2022 reprint (p.302): "Recall that all algebraic groups are affine."
- Definition 5.5, p.99 (same page in the 2022 reprint): "A homomorphism of algebraic groups is
  a quotient map if it is faithfully flat." Definition 5.41, p.108 (same page in the 2022
  reprint): "A homomorphism of algebraic groups is an embedding if it is a closed immersion." An exact sequence `e → N → G → Q → e` of algebraic
  groups (used in 5.48, 5.59 and 8.1, and in the proof of 15.39) is one in which `N → G` is an
  embedding onto the kernel of the quotient map `G → Q`.

The official errata snapshot of 2026-11-02 for the 2017 printing (source ID
`milne-2017-algebraic-groups-errata-2026-11-02`) has, for p.317, the entry "Delete 15.29 and
15.30. The proofs in Section 15h have been rewritten." Section 15h contains Theorem 15.39. Its
statement is unchanged in the 2022 reprint (apart from the wording noted above). The errata
snapshot of 2026-11-04 for the 2022 reprint (source ID
`milne-2022-algebraic-groups-errata-2026-11-04`) has an entry for p.322 affirming the statement
of Theorem 15.39 and flagging that its proof apparently assumes that the kernel `G'` is
connected. The Lean statement retains the theorem's hypothesis on the quotient `Q` alone. The
p.321 entry about commutativity in 15.37 concerns a different theorem.

In the reprint's induction diagram on p.323, `G_1` is the inverse image in `G` of a subgroup
`N` of `G''`, the quotient in Milne's notation. The sequence is
`e → G_1 → G → G''/N → e`: the middle group is `G`, and `G/G_1` is identified with `G''/N`.
Dimension alone does not decrease when `G''` is finite and `N = μ_p`; in that case the order
(length over `k`) drops by a factor of `p`. The Library route below does not rely on this
induction.

## Derivation from the source

- **Algebraic groups over `k`.** Milne's algebraic groups are group schemes of finite type over
  `k`, affine by the Chapter 15 convention. The statement assumes this for `G`. For `N` and `Q`
  it follows from `IsMultiplicativeType`, which gives finite type and affineness after a field
  extension, hence over `k`.
- **The extension.** `IsClosedSubgroup i` is Milne's embedding. `IsFppfQuotient (range i) q`
  says that `q` is flat and surjective, so faithfully flat (Milne's quotient map), locally of
  finite presentation (automatic for algebraic groups over a field), and has kernel `N`.
- **Multiplicative type, connected.** `IsMultiplicativeType N`, `IsMultiplicativeType Q` and
  `ConnectedSpace Q.X.left`. Over a field, connectedness of the group `Q` is geometric
  connectedness, since `Q` has a rational point.
- **Conclusion.** `IsMultiplicativeType G`.

## Related Library results

- [`multiplicativeTypeFieldExtension`](MultiplicativeTypeFieldExtensionProof.md) proves the
  broader [`MultiplicativeTypeFieldExtensionStatement`](MultiplicativeTypeFieldExtensionStatement.md)
  (SGA 3, Exposé IX, Proposition 8.2). Its first clause applies with the connected-quotient
  alternative; `IsClosedSubgroup.mono_overHom` supplies the required monomorphism of `i`.
- [`CentralTorusExtensionStatement`](CentralExtensionStatement.md) (Milne 12.41, 12.22): a central
  extension of a torus by a torus is a torus.
- [`MultiplicativeTypeExtensionActionStatement`](MultiplicativeTypeExtensionActionStatement.md)
  (Milne 12.41 with the errata hypothesis): connected groups act trivially on central
  extensions of groups of multiplicative type.
- [`MultiplicativeTypeFpqcExtensionStatement`](MultiplicativeTypeFpqcExtensionStatement.md)
  (Conrad B.4.2) states, over any base, that an extension of groups of multiplicative type is
  of multiplicative type when every fibre of the middle group is connected or commutative. Its
  hypothesis is on the middle group `G`. Theorem 15.39 instead assumes that the quotient `Q`
  is connected, and `G` may a priori be neither connected nor commutative; commutativity of
  `G` is part of the conclusion.
