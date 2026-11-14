# Statement: unirational Cartan subgroups give a unirational group

Worker 75.

`Langlands.GroupScheme.CartanUnirationalityStatement.{u} : Prop` is a statement-only,
`Prop`-valued definition. This module does not prove it, and it adds no other definitions,
theorems or axioms. It imports:

- [`Cartan.Basic`](Basic.md), for the group-scheme vocabulary over a field and the predicate
  `IsCartanSubgroup`.
- [`PointTopology.UnirationalDensity`](../../AlgebraicGeometry/PointTopology/UnirationalDensity.md),
  for `IsUnirational`.

## Lean statement

```lean
def CartanUnirationalityStatement : Prop :=
  ∀ (k : Type u) [Field k] [Infinite k] (G : GroupScheme (Spec (CommRingCat.of k))),
    Smooth G.X.hom → IsAffineHom G.X.hom → ConnectedSpace G.X.left →
    (∀ (C : GroupScheme (Spec (CommRingCat.of k))) (c : C ⟶ G),
      IsCartanSubgroup c → IsUnirational k C.X) →
    IsUnirational k G.X
```

The namespace `Langlands.AlgebraicGeometry.PointTopology` is open, so `IsUnirational` is the
declaration of that namespace.

## Objects and predicates used

- **Group schemes.** `GroupScheme S` is `Grp (Over S)`. For `G : GroupScheme S`, `G.X` is its
  scheme over `S`, an object of `Over S`; `G.X.left` is the underlying scheme and `G.X.hom` its
  structure morphism to `S`. A morphism `c : C ⟶ G` is a homomorphism of group schemes over
  `S`.
- `Smooth G.X.hom`, `IsAffineHom G.X.hom`: Mathlib's smooth and affine morphisms of schemes.
  `ConnectedSpace G.X.left`: the underlying topological space of `G` is connected (and so
  nonempty).
- `Infinite k`: the field `k` has infinitely many elements.
- `IsCartanSubgroup c` (module [`Cartan.Basic`](Basic.md)): `c` is a closed subgroup embedding
  (`IsClosedSubgroup c`) and there is a maximal torus `j : T.toGrp ⟶ G` (`IsMaximalTorus j`)
  such that `SubgroupFunctor.range c = torusCentralizer j`, an equality of subgroup functors
  on all schemes over `Spec k`. So `c` is a closed representative of the scheme-theoretic
  centralizer of a maximal torus of `G`.
- `IsUnirational k X`: for some finite type `ι : Type u`, there are a nonempty open subscheme
  `U` of the affine space `𝔸(ι; Spec k)` and a morphism `U ⟶ X` over `Spec k` whose underlying
  map of schemes has dense image.

## Statement and quantifiers

For every infinite field `k : Type u` and every group scheme `G` over `Spec k` that is smooth,
affine and connected over `k`: if every Cartan subgroup of `G` is unirational over `k`, then
`G` is unirational over `k`.

The hypothesis on Cartan subgroups ranges over every group scheme `C` over `Spec k` and every
homomorphism `c : C ⟶ G` with `IsCartanSubgroup c`, and asks that `C.X` be unirational over
`k`. Two Cartan embeddings with the same image are isomorphic over `G`
(`IsCartanSubgroup.existsUnique_iso_of_range_eq` in [`Cartan.Basic`](Basic.md)), so this is a
condition on the Cartan subgroups of `G` as subgroups, not on a choice of representative.

The trivial group is included: it is unirational through `𝔸(∅) = Spec k`.

## Source

James S. Milne, *Algebraic Groups: The theory of group schemes of finite type over a field*
(Cambridge University Press, 2017), source ID `milne-2017-algebraic-groups`, file
`Milne--Algebraic groups, the theory of group schemes of finite type over a field
(book)--2017.pdf`. Page numbers are printed page numbers; the PDF page is the printed page
plus 16.

- Corollary 17.92, p.382: "Let G be a connected group variety over an infinite field. If the
  Cartan subgroups of the maximal tori in G are unirational over k, then G is unirational over
  k (and G(k) is dense in G if k is infinite)."
- p.381, before Proposition 17.90: "Let G be a connected group variety. Recall (17.43, 17.44)
  that the Cartan subgroups of G are the centralizers of maximal tori of G, and that they are
  smooth, connected, and nilpotent."
- Definition 17.43, p.364: a Cartan subgroup of a connected group variety is the centralizer
  of a maximal torus.
- Chapter 17 opening, p.352: "Recall also that all algebraic groups are affine over a base
  field k."
- p.13, after Proposition 1.26: "Therefore 'group variety' = 'smooth algebraic group'."
- Definition 12.59, p.250: an irreducible variety `X` is unirational if its function field is
  contained in a purely transcendental extension of `k`; "Equivalently, X is ... unirational
  if there exists ... a surjective regular map from an open subset of some affine space Aⁿ to
  an open subset of X."

The official errata snapshot of 2026-11-02 (source ID
`milne-2017-algebraic-groups-errata-2026-11-02`) lists Chapter 17 corrections only on
pp.360, 364 and 386 (the text before 17.28, Example 17.42 and Exercise 17-7). It has no
correction to Definition 17.43 or Corollary 17.92.

Milne's proof: by Theorem 17.91 (generation of `G` by its Cartan subgroups), there is a
dominant morphism `C₁ × ⋯ × Cₘ → G` given by multiplication, with each `Cᵢ` a Cartan subgroup;
a product of unirational varieties is unirational, and so `G` is unirational. This is
explanation only; the statement does not depend on that route.

## Derivation from the source

- **Infinite field.** Milne states the corollary over an infinite field, and the statement
  keeps that hypothesis as `[Infinite k]`. (Milne's proof of 17.91 is written out only for
  infinite fields; the finite case is referred to Borel and Springer.)
- **Connected group variety.** An algebraic group in Milne is a group scheme of finite type
  over `k` (Definition 1.1, p.6), and in Chapter 17 algebraic groups are affine (the convention
  above). A connected group variety in Chapter 17 is therefore a smooth, affine, connected
  group scheme over `k`; the statement assumes exactly `Smooth G.X.hom`, `IsAffineHom G.X.hom`
  and `ConnectedSpace G.X.left`. Smoothness gives local finite presentation, and affineness
  gives quasi-compactness, so such a group scheme is of finite type.
- **Cartan subgroups of the maximal tori.** These are the centralizers of the maximal tori of
  `G` (Definition 17.43), which is the Library's `IsCartanSubgroup`. Milne's Cartan subgroups
  are smooth and connected (17.44), so unirationality of them is meaningful in the sense of
  Definition 12.59; the Lean hypothesis asks for `IsUnirational k C.X` directly.
- **Unirationality.** The statement uses the geometric equivalent in Definition 12.59 through
  the Library's `IsUnirational`: a morphism from a nonempty open subscheme of `𝔸ⁿ` with dense
  image. For an irreducible variety (such as a smooth connected group scheme over a field, or
  a Cartan subgroup) the two conditions agree: a map onto a nonempty open subset has dense
  image; conversely, the image of a dominant morphism of varieties contains a dense open
  subset (Chevalley's theorem), and restricting to its preimage gives a surjection onto it.

## Scope

- Milne's parenthetical assertion (density of `G(k)` in `G`) is not part of this statement. It
  follows from the conclusion through the Library theorem
  `IsUnirational.hasDenseRationalPoints` (module
  [`PointTopology.UnirationalDensity`](../../AlgebraicGeometry/PointTopology/UnirationalDensity.md)).
- Finite fields are not covered, as in Milne's corollary.
- Milne's primary definition of unirationality, through the function field `k(G)`, is not used.

## Related Library results

- [`Cartan.GenerationStatement`](GenerationStatement.md) states Milne's Theorem 17.91 over
  infinite fields (a smooth connected affine group is generated by its Cartan subgroups), the
  input to Milne's proof of the corollary.
- [`Cartan.StructureStatement`](StructureStatement.md) states Milne's Proposition 17.44 (Cartan
  subgroups are smooth, connected and nilpotent).
- [`Reductive.TorusDominationStatement`](../Reductive/TorusDominationStatement.md) states that a
  connected reductive group over an infinite field receives a dominant morphism from a torus,
  the structural step of Milne's proof in the reductive case.
