# Statement: fixed subgroups of torus actions on connected group varieties

Worker 75.

`Langlands.GroupScheme.TorusActionFixedSubgroupStatement.{u} : Prop` is a statement-only,
`Prop`-valued definition. This module does not prove it, and it adds no other definitions,
theorems or axioms. It imports:

- [`AutomorphicAction`](../AutomorphicAction.md), for `AutomorphicAction` and its all-test
  fixed subgroup functor `AutomorphicAction.fixedSubgroup`.
- [`Reductive.UnipotentRadical`](../Reductive/UnipotentRadical.md), for `IsUnipotentRadical`
  and, through its imports, `IsClosedSubgroup`, `IsConnectedReductive` and the group-scheme
  vocabulary over a field.
- [`Torus.Lattice`](../Torus/Lattice.md), for the field-level torus predicate `IsTorus`.

## Lean statement

```lean
def TorusActionFixedSubgroupStatement : Prop :=
  ∀ (k : Type u) [Field k] (G : GroupScheme (Spec (CommRingCat.of k)))
    [Smooth G.X.hom] [IsAffineHom G.X.hom] [ConnectedSpace G.X.left]
    (S : GroupScheme (Spec (CommRingCat.of k))), IsTorus S →
    ∀ (a : AutomorphicAction S G) (C : GroupScheme (Spec (CommRingCat.of k))) (c : C ⟶ G),
      a.fixedSubgroup.IsRepresentedBy c → IsClosedSubgroup c →
      (Smooth C.X.hom ∧ ConnectedSpace C.X.left) ∧
      (IsConnectedReductive G → IsConnectedReductive C) ∧
      (IsAlgClosed k →
        ∀ (U : GroupScheme (Spec (CommRingCat.of k))) (u : U ⟶ G), IsUnipotentRadical u →
        ∀ (V : GroupScheme (Spec (CommRingCat.of k))) (v : V ⟶ C), IsUnipotentRadical v →
          SubgroupFunctor.range (v ≫ c) = SubgroupFunctor.range u ⊓ a.fixedSubgroup)
```

## Objects and predicates used

- **Group schemes.** `GroupScheme S` is `Grp (Over S)`. For `G : GroupScheme S`, `G.X.left`
  is the underlying scheme and `G.X.hom` its structure morphism.
- `Smooth`, `IsAffineHom`, `ConnectedSpace`, `IsAlgClosed`: as in Mathlib.
- `IsTorus` ([`Torus.Lattice`](../Torus/Lattice.md)): a group scheme over `k` that becomes a
  split torus after base change to some field extension of `k` (Milne 12.14).
- `AutomorphicAction S G` ([`AutomorphicAction`](../AutomorphicAction.md)): a morphism
  `hom : S.X ⊗ G.X ⟶ G.X` over the base which, on the points over every scheme `T` over the
  base, is a group action of `S(T)` on `G(T)` by group homomorphisms (laws `one_left`,
  `mul_left`, `mul_right`). `a.act h g` is the action of the point `h` on the point `g`.
- `a.fixedSubgroup` ([`AutomorphicAction`](../AutomorphicAction.md)): the subgroup functor of
  `G` whose points over `T` are the `g : T ⟶ G.X` with `a.act h (b ≫ g) = b ≫ g` for every
  `b : T' ⟶ T` and every point `h : T' ⟶ S.X` (`AutomorphicAction.IsFixed`).
- `F.IsRepresentedBy c` ([`SubgroupFunctor`](../SubgroupFunctor.md)): `c` is a monomorphism and
  `SubgroupFunctor.range c = F`.
- `IsClosedSubgroup c` ([`Reductive.Basic`](../Reductive/Basic.md)): the underlying morphism of
  schemes of `c` is a closed immersion.
- `IsConnectedReductive G` ([`Reductive.Basic`](../Reductive/Basic.md)): `G` is smooth, affine
  and connected, and the base change of `G` to `AlgebraicClosure k` has trivial unipotent
  radical (`HasTrivialUnipotentRadical`: every smooth connected unipotent normal closed subgroup
  is trivial).
- `IsUnipotentRadical u` ([`Reductive.UnipotentRadical`](../Reductive/UnipotentRadical.md)):
  `u` is a closed subgroup, `U` is smooth, connected and unipotent (`IsUnipotent`,
  [`Reductive.Basic`](../Reductive/Basic.md): every nonzero finite-dimensional representation
  has a nonzero fixed vector), `range u` is normal, and `range u` contains the range of every
  smooth connected unipotent normal closed subgroup.
- `SubgroupFunctor.range f`: the points of `G` that factor through `f`; `⊓` is the pointwise
  intersection of subgroup functors.

## Statement and quantifiers

For every field `k : Type u`, every smooth, affine, connected group scheme `G` over `Spec k`,
every torus `S` over `k`, every action `a` of `S` on `G` by group automorphisms, and every
closed subgroup `c : C ⟶ G` representing the fixed subgroup functor `G^S`:

1. `C` is smooth and its underlying space is connected;
2. if `G` is connected reductive, then `C` is connected reductive;
3. if `k` is algebraically closed, then for every unipotent radical `u : U ⟶ G` of `G` and
   every unipotent radical `v : V ⟶ C` of `C`, the image of `V` in `G` is the intersection
   of `U` with `G^S`, as subgroup functors of `G` on all schemes over `Spec k`:
   `R_u(G^S) = R_u(G) ∩ G^S = R_u(G)^S`.

The statement takes `C`, `U` and `V` as given representatives. It does not assert that they
exist.

## Source

James S. Milne, *Algebraic Groups: The theory of group schemes of finite type over a field*
(Cambridge University Press, 2017), source ID `milne-2017-algebraic-groups`, file
`Milne--Algebraic groups, the theory of group schemes of finite type over a field
(book)--2017.pdf`. Page numbers are printed page numbers; the PDF page is the printed page
plus 16. The quoted statements have the same wording and printed pages in the 2022 corrected
reprint (source ID `milne-2022-algebraic-groups`), except where noted.

- Theorem 13.9, p.257: "Let H be a linearly reductive group variety acting on a smooth
  algebraic group G. Then G^H is smooth." The proof of Corollary 13.10, p.257, recalls:
  "Recall (12.30) that multiplicative groups are linearly reductive."
- Remark 17.40(a), p.364: "More generally, if T is a torus acting on a connected group
  variety G, then G^T is connected. This follows from Lemma 17.38 applied to G ⋊ T." The 2022
  reprint (p.364) reads "Theorem 17.38", which is the correct label.
- Section 17d, opening, p.363: "The base field k need not be algebraically closed." The 2022
  reprint (p.363) reads: "The field k is not required to be algebraically closed."
- Section 17g, opening, p.370: "In this section, G is a connected group variety over k."
- Corollary 17.58, p.371: "Assume that k is algebraically closed, and let S be a torus acting
  on G. Then R_u(G^S) = R_u(G)^S."
- Corollary 17.59, p.371: "Let S be a torus acting on G. If G is reductive, then so also is
  G^S. In particular, the centralizer of a torus in a reductive group is reductive."
- Theorem 7.1, p.138, for an action of a group functor `G` on a separated algebraic scheme
  `X`: "The functor X^G, R ↦ {x ∈ X(R) | μ(g, x_{R'}) = x_{R'} for all g ∈ G(R') and all
  R-algebras R'} is represented by a closed subscheme of X." P.139: "The subscheme X^G is
  called the fixed subscheme for the action. Directly from its definition, one sees that its
  formation commutes with extension of the base field." The 2022 reprint (pp.138-139) lists
  the two quantifiers in the other order, says "a closed subscheme X^G of X", and calls X^G
  the "fixed-point subscheme".
- p.50, before the definition of `N ⋊_θ Q`: "Let N and Q be algebraic groups, and suppose that
  there is given an action of Q on N ... such that, for every q, the map n ↦ θ_R(q, n) is a
  group homomorphism."
- 6.46, p.135: "Let G be a connected group variety over k. ... among the connected normal
  unipotent subgroup varieties of G, there is a largest one. This is called the unipotent
  radical R_u(G) of G. ... A connected group variety over a field k is said to be reductive if
  G_{k^a} is reductive, i.e., if its geometric unipotent radical R_u(G_{k^a}) is trivial."
- Chapter 17 opening, p.352: "Recall also that all algebraic groups are affine over a base
  field k"; remark after 1.26, p.13 (p.14 in the 2022 reprint): "“group variety” = “smooth
  algebraic group”."

The official errata snapshot of 2026-11-02 for the 2017 printing (source ID
`milne-2017-algebraic-groups-errata-2026-11-02`) has no entry for pp.13, 50, 135, 138, 139,
257, 352, 363, 370 or 371; its only p.364 entry concerns Example 17.42. The errata snapshot of
2026-11-04 for the 2022 reprint (source ID `milne-2022-algebraic-groups-errata-2026-11-04`)
has no entry for the corresponding reprint pages 14, 50, 135, 138, 139, 257, 352, 363, 364,
370 or 371.

Milne's proofs, as explanation only:

- Corollary 17.58: put `G' = G ⋊ S`; then `R_u(G') = R_u(G)`, and Corollary 17.57 (the
  unipotent radical of a torus centralizer, stated in the Library as
  `TorusCentralizerUnipotentRadicalStatement`) applied to `S ⊆ G'` gives
  `R_u(G^S) = R_u(C_{G'}(S)) = R_u(G') ∩ C_{G'}(S) = R_u(G)^S`. Milne writes
  `C_{G'}(S) = G^S`; in fact `C_{G'}(S) = G^S ⋊ S`, which is `G^S × S` because `S` is
  commutative and fixes `G^S`. The argument is unaffected: a torus has no nontrivial unipotent
  subgroup, so `R_u(G^S × S) = R_u(G^S)`, and `R_u(G) ∩ (G^S × S) = R_u(G) ∩ G^S`.
- Corollary 17.59: `G^S` is smooth and connected (13.9, 17.40), and its geometric unipotent
  radical is `R_u(G_{k^a})^S = e`. The 2017 printing cites "Corollary 17.57 applied to
  `G_{k^a}`" and the 2022 reprint "Corollary 17.59 applied to `G_{k^a}`" for this step; the
  step is Corollary 17.58.

## Derivation from the source

- **Connected group variety.** `[Smooth G.X.hom]`, `[IsAffineHom G.X.hom]`,
  `[ConnectedSpace G.X.left]`: Section 17g assumes `G` is a connected group variety, Chapter
  17 assumes algebraic groups are affine, and Remark 17.40(a) assumes `G` is a connected group
  variety. Over a field a group scheme has a rational point, so connectedness is geometric
  connectedness. Clauses 1 and 2 are stated over any field, as Section 17d allows; clause 3
  assumes `IsAlgClosed k`, as Corollary 17.58 does.
- **A torus acting on `G`.** `IsTorus S` and an `AutomorphicAction S G`: an action of `S` on
  `G` such that every point of `S` acts by a group homomorphism, the notion of p.50 used to
  form `G ⋊ S` in 17.40(a) and 17.58.
- **`G^S`.** Any closed subgroup `c` representing `a.fixedSubgroup`. The fixed subgroup functor
  is Milne's functor `X^G` of Theorem 7.1 for `X = G` and the acting group `S`: a point is
  fixed when it is fixed by every point of `S` after every base change.
- **Clause 1.** Smoothness is Theorem 13.9 for `H = S`, since tori are linearly reductive
  (12.30, recalled in the proof of 13.10). Connectedness is Remark 17.40(a).
- **Clause 2.** Milne's "reductive" (6.46) for a connected group variety over `k` is
  triviality of the geometric unipotent radical, which is `IsConnectedReductive`; Corollary
  17.59's hypothesis "G reductive" includes that `G` is a connected group variety.
- **Clause 3.** Milne's `R_u` (6.46) is the largest connected normal unipotent subgroup
  variety; this is `IsUnipotentRadical`. Both sides are compared as subgroup functors of `G`:
  the radical of `C` is transported into `G` along `c`, and `R_u(G)^S` is written as the
  pointwise intersection `range u ⊓ a.fixedSubgroup`, whose points are the points of `R_u(G)`
  fixed by `S`. Milne proves the equality of algebraic subgroups.

## Related Library results

- [`Diagonalizable.FixedSubgroupSmoothStatement`](../Torus/DiagonalizableFixedSmoothStatement.md)
  states that closed representatives of fixed subgroups of actions of split diagonalizable
  groups on smooth affine groups are smooth. For split `S` this contains the smoothness part
  of clause 1.
- [`IsTorus.connectedSpace_centralizer`](../Torus/CentralizerConnected.md) proves that every
  representative of a torus centralizer in a smooth connected affine group is connected
  (Milne 17.38). By `AutomorphicAction.conjugation_fixedSubgroup_eq_torusCentralizer`
  ([`AutomorphicAction`](../AutomorphicAction.md)), this is the connectedness part of clause
  1 for conjugation actions.
- [`TorusCentralizerUnipotentRadicalStatement`](TorusCentralizerUnipotentRadicalStatement.md)
  is Milne 17.57, the case of clause 3 for the conjugation action of a closed torus.
- [`MultiplicativeTypeCentralizerReductiveStatement`](../Torus/MultiplicativeTypeCentralizerReductiveStatement.md)
  and [`DynamicCentralizerReductiveStatement`](../Dynamic/CentralizerReductiveStatement.md)
  state reductivity of centralizers in connected reductive groups, the conjugation case of
  clause 2.
- [`Torus.SolvableFixedContainmentConnectedStatement`](../Torus/SolvableFixedContainmentConnectedStatement.md)
  and [`TorusStableUnipotentSubgroupConnectedStatement`](../Unipotent/TorusStableSubgroupConnectedStatement.md)
  state connectedness for split-torus actions on smooth connected solvable groups and for torus
  actions on connected unipotent groups.
