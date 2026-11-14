# Statement: unirationality of connected group varieties

Worker 75.

`Langlands.GroupScheme.ConnectedGroupUnirationalityStatement.{u} : Prop` is a statement-only,
`Prop`-valued definition. This module does not prove it, and it adds no other definitions,
theorems or axioms. It imports:

- [`Reductive.Basic`](../Reductive/Basic.md), for the group-scheme vocabulary over a field and
  the predicate `IsConnectedReductive`.
- [`PointTopology.UnirationalDensity`](../../AlgebraicGeometry/PointTopology/UnirationalDensity.md),
  for `IsUnirational`.
- Mathlib's `Mathlib.FieldTheory.Perfect`, for `PerfectField`.

## Lean statement

```lean
def ConnectedGroupUnirationalityStatement : Prop :=
  ∀ (k : Type u) [Field k] (G : GroupScheme (Spec (CommRingCat.of k))),
    (PerfectField k → Smooth G.X.hom → IsAffineHom G.X.hom → ConnectedSpace G.X.left →
      IsUnirational k G.X) ∧
    (IsConnectedReductive G → IsUnirational k G.X)
```

The namespace `Langlands.AlgebraicGeometry.PointTopology` is open, so `IsUnirational` is the
declaration of that namespace.

## Objects and predicates used

- **Group schemes.** `GroupScheme S` is `Grp (Over S)`. For `G : GroupScheme S`, `G.X` is its
  scheme over `S`, an object of `Over S`; `G.X.left` is the underlying scheme and `G.X.hom` its
  structure morphism to `S`.
- `Smooth G.X.hom`, `IsAffineHom G.X.hom`: Mathlib's smooth and affine morphisms of schemes.
  `ConnectedSpace G.X.left`: the underlying topological space of `G` is connected (and so
  nonempty).
- `PerfectField k`: Mathlib's perfect fields (every irreducible polynomial is separable).
- `IsConnectedReductive G` (module `Reductive.Basic`): `G` is smooth, affine and connected over
  `k`, and the base change of `G` to an algebraic closure of `k` has trivial unipotent radical.
- `IsUnirational k X`: for some finite type `ι : Type u`, there are a nonempty open subscheme
  `U` of the affine space `𝔸(ι; Spec k)` and a morphism `U ⟶ X` over `Spec k` whose underlying
  map of schemes has dense image.

## Statement and quantifiers

For every field `k : Type u` and every group scheme `G` over `Spec k`, the following two
assertions hold.

1. If `k` is perfect and `G` is smooth, affine and connected over `k`, then `G` is
   unirational: there are a finite type `ι`, a nonempty open subscheme `U` of `𝔸(ι; Spec k)`
   and a morphism `U ⟶ G.X` over `Spec k` with dense image.
2. If `G` is connected reductive, then `G` is unirational in the same sense. The field `k` is
   arbitrary here: it may be imperfect or finite.

Both parts include the trivial group, which is unirational through `𝔸(∅) = Spec k`.

## Source

James S. Milne, *Algebraic Groups: The theory of group schemes of finite type over a field*
(Cambridge University Press, 2017), source ID `milne-2017-algebraic-groups`, file
`Milne--Algebraic groups, the theory of group schemes of finite type over a field
(book)--2017.pdf`. Page numbers are printed page numbers; the PDF page is the printed page
plus 16.

- Theorem 17.93, p.382: "Let G be a connected group variety over k. Then G is unirational
  over k (and G(k) is dense in G if k is infinite) under each of the following hypotheses:
  (a) k is perfect; (b) G is reductive."
- Chapter 17 opening, p.352: "Recall also that all algebraic groups are affine over a base
  field k."
- p.13, after Proposition 1.26: "Therefore 'group variety' = 'smooth algebraic group'."
- 6.46, p.135 (in §6.h, where "all algebraic groups are affine"): "A connected group variety
  over a field k is said to be reductive if G_{k^a} is reductive, i.e., if its geometric
  unipotent radical R_u(G_{k^a}) is trivial."
- Definition 12.59, p.250: an irreducible variety `X` is unirational if its function field is
  contained in a purely transcendental extension of `k`; "Equivalently, X is ... unirational
  if there exists ... a surjective regular map from an open subset of some affine space Aⁿ to
  an open subset of X."

The official errata snapshot of 2026-11-02 (source ID
`milne-2017-algebraic-groups-errata-2026-11-02`) lists Chapter 17 corrections only on
pp.360, 364 and 386 (the text before 17.28, 17.42 and Exercise 17-7). It has no correction to
Theorem 17.93.

Milne proves part (a) through Corollary 17.92 (a connected group variety is unirational when
the Cartan subgroups of its maximal tori are), the structure of Cartan subgroups over a perfect
field (16.48: products of a torus and a connected unipotent group), the unirationality of tori
(12.64) and of connected unipotent groups over a perfect field (14.66). He proves part (b)
from 17.84 (the Cartan subgroups of a reductive group are its maximal tori) and 12.64. This is
explanation only; the statement does not depend on that route.

## Derivation from the source

- **Connected group variety.** An algebraic group in Milne is a group scheme of finite type
  over `k` (Definition 1.1, p.6), and from Chapter 9 onward algebraic groups are affine (the
  Chapter 17 convention above). A connected group variety in Chapter 17 is therefore a smooth,
  affine, connected group scheme over `k`. Smoothness gives local finite presentation, and
  affineness gives quasi-compactness, so such a group scheme is of finite type. Part 1 assumes
  exactly `Smooth G.X.hom`, `IsAffineHom G.X.hom` and `ConnectedSpace G.X.left`.
- **Why affineness is kept in part 1.** Without affineness the assertion is false: an elliptic
  curve over a perfect field is a smooth connected group scheme of finite type, but it is not
  unirational, since a unirational curve is rational (Lüroth's theorem) and an elliptic curve
  has genus 1.
- **Reductive groups.** Milne's reductive groups (6.46) are connected affine group varieties
  whose geometric unipotent radical is trivial. This is the Library's `IsConnectedReductive`,
  which includes smoothness, affineness and connectedness. Part 2 therefore has no separate
  smoothness, affineness or connectedness hypotheses.
- **Unirationality.** The statement uses the geometric equivalent in Definition 12.59. The
  Library's `IsUnirational` asks for a morphism from a nonempty open subscheme of `𝔸ⁿ` with
  dense image. A smooth connected group scheme over a field is irreducible, so `G` is an
  irreducible variety. For an irreducible variety the two conditions agree: a map onto a
  nonempty open subset has dense image; conversely, the image of a dominant morphism of
  varieties contains a dense open subset (Chevalley's theorem), and restricting to its
  preimage gives a surjection onto it.

## Scope

- Milne's parenthetical assertion (density of `G(k)` in `G` when `k` is infinite) is not part
  of this statement. It follows from the conclusion through the Library theorem
  `IsUnirational.hasDenseRationalPoints` (module
  [`PointTopology.UnirationalDensity`](../../AlgebraicGeometry/PointTopology/UnirationalDensity.md)).
- Milne's primary definition of unirationality, through the function field `k(G)`, is not used.
- Corollary 17.92 and Remark 17.94 are not stated.

## Related Library results

- [`Reductive.RationalPointDensityStatement`](../Reductive/RationalPointDensityStatement.md)
  states the density consequence of part 2: over an infinite field, the rational points of a
  connected reductive group are Zariski dense.
- [`Rational.MaximalTorusParameterUnirationalStatement`](MaximalTorusParameterUnirationalStatement.md)
  states that the scheme parametrizing maximal tori of a smooth connected affine group over any
  field is unirational (SGA 3, Exposé XIV, Théorème 6.1). That is a different scheme from `G`.
