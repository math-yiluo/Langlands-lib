# Statement: the unipotent radical of the centralizer of a torus

Worker 75.

`Langlands.GroupScheme.TorusCentralizerUnipotentRadicalStatement.{u} : Prop` is a
statement-only, `Prop`-valued definition. This module does not prove it, and it adds no other
definitions, theorems or axioms. It imports:

- [`Reductive.UnipotentRadical`](../Reductive/UnipotentRadical.md), for `IsUnipotentRadical`
  and, through its imports, `IsClosedSubgroup` and the group-scheme vocabulary over a field.
- [`Rational.TorusCentralizer`](../Rational/TorusCentralizer.md), for `torusCentralizer`.
- [`Torus.Lattice`](../Torus/Lattice.md), for the field-level torus predicate `IsTorus`.

## Lean statement

```lean
def TorusCentralizerUnipotentRadicalStatement : Prop :=
  ∀ (k : Type u) [Field k] [IsAlgClosed k] (G : GroupScheme (Spec (CommRingCat.of k)))
    [Smooth G.X.hom] [IsAffineHom G.X.hom] [ConnectedSpace G.X.left]
    (S : CommGroupScheme (Spec (CommRingCat.of k))) (s : S.toGrp ⟶ G),
    IsTorus S.toGrp → IsClosedSubgroup s →
    ∀ (C : GroupScheme (Spec (CommRingCat.of k))) (c : C ⟶ G),
      (torusCentralizer s).IsRepresentedBy c → IsClosedSubgroup c →
    ∀ (U : GroupScheme (Spec (CommRingCat.of k))) (u : U ⟶ G), IsUnipotentRadical u →
    ∀ (V : GroupScheme (Spec (CommRingCat.of k))) (v : V ⟶ C), IsUnipotentRadical v →
      SubgroupFunctor.range (v ≫ c) = SubgroupFunctor.range u ⊓ SubgroupFunctor.range c
```

## Objects and predicates used

- **Group schemes.** `GroupScheme S` is `Grp (Over S)` and `CommGroupScheme S` its commutative
  version, with `S.toGrp` the underlying group scheme. For `G : GroupScheme S`, `G.X.left` is
  the underlying scheme and `G.X.hom` its structure morphism.
- `Smooth`, `IsAffineHom`, `ConnectedSpace`: as in Mathlib.
- `IsTorus` ([`Torus.Lattice`](../Torus/Lattice.md)): a group scheme over `k` that becomes a
  split torus after base change to some field extension of `k` (Milne 12.14).
- `IsClosedSubgroup f` ([`Reductive.Basic`](../Reductive/Basic.md)): the underlying morphism of
  schemes of `f` is a closed immersion.
- `torusCentralizer s` ([`Rational.TorusCentralizer`](../Rational/TorusCentralizer.md)): the
  centralizer `C_G(S)`; a point `g` over `U` lies in it when, after every base change
  `a : V ⟶ U`, `a ≫ g` commutes with every point of `S` over `V`.
- `F.IsRepresentedBy c` ([`SubgroupFunctor`](../SubgroupFunctor.md)): `c` is a monomorphism and
  `SubgroupFunctor.range c = F`.
- `IsUnipotentRadical u` ([`Reductive.UnipotentRadical`](../Reductive/UnipotentRadical.md)):
  `u` is a closed subgroup, `U` is smooth, connected and unipotent (`IsUnipotent`,
  [`Reductive.Basic`](../Reductive/Basic.md): every nonzero finite-dimensional representation
  has a nonzero fixed vector), `range u` is normal, and `range u` contains the range of every
  smooth connected unipotent normal closed subgroup.
- `SubgroupFunctor.range f`: the points of `G` that factor through `f`; `⊓` is the pointwise
  intersection of subgroup functors.

## Statement and quantifiers

For every algebraically closed field `k : Type u`, every smooth, affine, connected group scheme
`G` over `Spec k`, every closed torus `s : S ⟶ G`, every closed subgroup `c : C ⟶ G`
representing the centralizer `C_G(S)`, every unipotent radical `u : U ⟶ G` of `G` and every
unipotent radical `v : V ⟶ C` of `C`: the image of `V` in `G` is the intersection of `U` and
`C`, as subgroup functors of `G` on all schemes over `Spec k`:
`R_u(C_G(S)) = R_u(G) ∩ C_G(S)`.

## Source

James S. Milne, *Algebraic Groups: The theory of group schemes of finite type over a field*
(Cambridge University Press, 2017), source ID `milne-2017-algebraic-groups`, file
`Milne--Algebraic groups, the theory of group schemes of finite type over a field
(book)--2017.pdf`. Page numbers are printed page numbers; the PDF page is the printed page
plus 16.

- Corollary 17.57, p.371: "Assume that k is algebraically closed, and let S be a torus in G.
  Then R_u(C_G(S)) = R_u(G) ∩ C_G(S)."
- Section 17g, opening, p.370: "In this section, G is a connected group variety over k."
- 6.46, p.135: for a connected group variety `G`, the unipotent radical `R_u(G)` is the largest
  connected normal unipotent subgroup variety of `G`.
- Chapter 17 opening, p.352: all algebraic groups are affine over the base field; remark after
  1.26, p.13: "group variety" means "smooth algebraic group".

The official errata snapshot of 2026-11-02 (source ID
`milne-2017-algebraic-groups-errata-2026-11-02`) lists Chapter 17 corrections only on pp.360,
364 and 386 (the remark before 17.28, Example 17.42 and Exercise 17-7). None concerns
Corollary 17.57.

Milne's proof: `R_u(G) ∩ C_G(S) = R_u(G)^S` is smooth and connected (13.9, 17.40), unipotent
and normal in `C_G(S)`, so it lies in `R_u(C_G(S))`. Conversely, for a maximal torus
`T ⊇ S`, every Borel subgroup `B ⊇ T` of `G` meets `C_G(S)` in a Borel subgroup of `C_G(S)`
(17.46), so `R_u(C_G(S)) ⊆ (⋂_{B ⊇ T} B)°_red = R_u(G) · T` by Chevalley's theorem 17.56, and
hence `R_u(C_G(S)) ⊆ R_u(G)`. This is explanation only.

## Derivation from the source

- **Connected group variety over an algebraically closed field.** `[IsAlgClosed k]`,
  `[Smooth G.X.hom]`, `[IsAffineHom G.X.hom]`, `[ConnectedSpace G.X.left]`, as Corollary 17.57
  assumes in Section 17g.
- **A torus in `G`.** A torus `S` with a closed immersion `s` (`IsTorus S.toGrp`,
  `IsClosedSubgroup s`).
- **`C_G(S)`.** Any closed subgroup `c` representing `torusCentralizer s`.
- **Unipotent radicals.** Milne's `R_u` (6.46) is the largest connected normal unipotent
  subgroup variety; this is `IsUnipotentRadical`. The statement takes the radicals as given
  representatives `u` and `v`; it does not assert that they exist.
- **The equality.** Both sides are compared as subgroup functors of `G`: the radical of `C` is
  transported into `G` along `c`, and `R_u(G) ∩ C_G(S)` is the pointwise intersection, which
  is the scheme-theoretic intersection. Milne proves the equality of algebraic subgroups, with
  `R_u(G) ∩ C_G(S)` smooth.

## Related Library results

- [`Absolute.CentralizerUnipotentBorelContainmentStatement`](CentralizerUnipotentBorelContainmentStatement.md)
  states, for the centralizer of a cocharacter, that every smooth connected unipotent normal
  closed subgroup of the centralizer lies in every Borel subgroup containing the cocharacter.
- [`Torus.CentralizerConnected`](../Torus/CentralizerConnected.md) proves that every
  representative of a torus centralizer is connected (Milne 17.38).
