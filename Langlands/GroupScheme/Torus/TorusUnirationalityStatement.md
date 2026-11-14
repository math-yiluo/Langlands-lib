# Statement: rationality of Weil-restricted multiplicative groups and unirationality of tori

Worker 75.

`Langlands.GroupScheme.TorusUnirationalityStatement.{u} : Prop` is a statement-only,
`Prop`-valued definition. This module does not prove it, and it adds no other definitions,
theorems or axioms. It imports:

- [`Torus.WeilRestrictionCommutative`](WeilRestrictionCommutative.md). Through it, this
  module gets the Weil restriction `WeilGm.groupScheme A B` of the multiplicative group
  (module [`Torus.WeilRestriction`](WeilRestriction.md)) and the predicate `IsTorus` over a
  field (module [`Torus.Lattice`](Lattice.md)).
- [`PointTopology.UnirationalTransport`](../../AlgebraicGeometry/PointTopology/UnirationalTransport.md),
  which gives `HasFiniteAffineBirationalModel`. Through it, this module also gets
  `IsUnirational` (module
  [`PointTopology.UnirationalDensity`](../../AlgebraicGeometry/PointTopology/UnirationalDensity.md)).
- Mathlib's `Mathlib.RingTheory.Etale.Basic`, for `Algebra.Etale`.

## Lean statement

```lean
def TorusUnirationalityStatement : Prop :=
  ∀ (k : Type u) [Field k],
    (∀ (k' : Type u) [Field k'] [Algebra k k'] [FiniteDimensional k k'],
      HasFiniteAffineBirationalModel k (WeilGm.groupScheme (CommRingCat.of k) k').X) ∧
    (∀ T : GroupScheme (Spec (CommRingCat.of k)), IsTorus T → IsUnirational k T.X) ∧
    (∀ (A : Type u) [CommRing A] [Algebra k A] [Algebra.Etale k A] [Module.Finite k A],
      HasFiniteAffineBirationalModel k (WeilGm.groupScheme (CommRingCat.of k) A).X)
```

The namespace `Langlands.AlgebraicGeometry.PointTopology` is open, so
`HasFiniteAffineBirationalModel` and `IsUnirational` are the declarations of that namespace.

## Objects and predicates used

- **Group schemes.** `GroupScheme S` is `Grp (Over S)`. For `G : GroupScheme S`, `G.X` is
  its scheme over `S`, an object of `Over S`.
- **Weil restriction of `𝔾_m`.** For a commutative `k`-algebra `B` that is finite and
  projective as a `k`-module, `WeilGm.groupScheme (CommRingCat.of k) B` is a group scheme
  over `Spec k`. Its points over a test scheme `T` are the units of `B ⊗[k] Γ(T)`
  (`WeilGm.pointsEquiv`). This is Milne's `(𝔾_m)_{B/k}`. Every `k`-module is projective, so
  over a field only finiteness is assumed. In part 1 finiteness is `FiniteDimensional k k'`;
  in part 3 it is `Module.Finite k A`.
- `HasFiniteAffineBirationalModel k X`: for some finite type `ι : Type u`, the structure
  morphism `X.hom` is birational over `Spec k` to the affine space `𝔸(ι; Spec k) ⟶ Spec k`.
  The birational witness is Mathlib's `Scheme.PartialIso`: an isomorphism between a dense
  open subscheme of `X.left` and a dense open subscheme of `𝔸(ι; Spec k)`, compatible with
  the maps to `Spec k` (`Scheme.BirationalOver`).
- `IsUnirational k X`: for some finite type `ι : Type u`, there are a nonempty open
  subscheme `U` of `𝔸(ι; Spec k)` and a morphism `U ⟶ X` over `Spec k` whose underlying
  map has dense image.
- `IsTorus T`: there is a field extension `K` of `k` such that the base change `T_K` is a
  split torus, that is, isomorphic to `𝔾_m^I` over `K` for a finite type `I` (Milne's
  Definition 12.14).
- **Étale algebras.** `Algebra.Etale k A` is Mathlib's étale algebra (formally étale and of
  finite presentation). With `Module.Finite k A` this is Milne's étale `k`-algebra, a finite
  product of finite separable field extensions of `k` (see Derivation below).

## Statement and quantifiers

For every field `k : Type u`, the following three assertions hold.

1. For every field `k' : Type u` that is a finite extension of `k`, the Weil restriction
   `(𝔾_m)_{k'/k}` is birational over `k` to a finite-dimensional affine space.
2. For every torus `T` over `k`, there are a nonempty open subscheme `U` of some
   finite-dimensional affine space over `k` and a morphism `U ⟶ T` over `k` with dense image.
3. For every commutative `k`-algebra `A : Type u` that is étale and finite over `k`, the
   induced torus `(𝔾_m)_{A/k}` is birational over `k` to a finite-dimensional affine space.

No separability is assumed in part 1. Part 3 includes `A = 0`, for which `(𝔾_m)_{A/k}` is
`Spec k`, birational to `𝔸(∅) = Spec k`.

## Source

James S. Milne, *Algebraic Groups: The theory of group schemes of finite type over a field*
(Cambridge University Press, 2017), source ID `milne-2017-algebraic-groups`, file
`Milne--Algebraic groups, the theory of group schemes of finite type over a field
(book)--2017.pdf`. Page numbers are printed page numbers; the PDF page is the printed page
plus 16.

- Definition 12.59, p.250: "An irreducible variety X is said to be rational (resp.
  unirational) if its field of rational functions k(X) is a purely transcendental extension
  of k (resp. contained in a purely transcendental extension of k). Equivalently, X is
  rational (resp. unirational) if there exists an isomorphism (resp. a surjective regular
  map) from an open subset of some affine space Aⁿ to an open subset of X."
- Proposition 12.60, p.250: "Let k′ be a finite extension of k. The Weil restriction
  (𝔾_m)_{k′/k} of 𝔾_m is rational."
- Definition 12.62, p.251: "A torus is said to be induced (or quasi-split or quasi-trivial)
  if it is of the form (𝔾_m)_{A/k} for an étale k-algebra A."
- Proposition 12.64, p.251: "Every torus is unirational, and every induced torus is
  rational."
- p.14: "An étale k-algebra is a finite product of finite separable field extensions of k."
- Definition 12.14, p.236 (tori), as formalized by `IsTorus`.

The official errata snapshot of 2026-11-02 (source ID
`milne-2017-algebraic-groups-errata-2026-11-02`) lists corrections only to 12.41 and 12.57
in Chapter 12. It has no correction to 12.59, 12.60, 12.62 or 12.64.

Milne proves 12.60 by identifying the Weil restriction of `𝔸¹` with `𝔸ⁿ` through a
`k`-basis of `k'`, and `(𝔾_m)_{k'/k}` with the complement of the zero set of the norm
polynomial. He proves 12.64 by combining 12.60 with 12.63 (every torus is a quotient of an
induced torus). This is explanation only.

## Derivation from the source

- **Part 1 is Proposition 12.60.** A finite extension `k'` of `k` is a field `k'` with
  `[Algebra k k'] [FiniteDimensional k k']`. Rationality uses the geometric equivalent in
  Definition 12.59: an isomorphism from an open subset of some `𝔸ⁿ` onto an open subset of
  `X`. For an irreducible `X` and the irreducible `𝔸ⁿ`, nonempty open subsets are exactly the
  dense ones, so this is `Scheme.BirationalOver` with `𝔸(ι; Spec k)` for a finite `ι`, which
  is `HasFiniteAffineBirationalModel`. `(𝔾_m)_{k'/k}` is irreducible, as Milne's proof shows
  (an open subscheme of `𝔸ⁿ`).
- **Part 2 is the first half of Proposition 12.64.** Unirationality uses the geometric
  equivalent in Definition 12.59: a surjective regular map from an open subset of `𝔸ⁿ` onto
  an open subset of `X`. The Library's `IsUnirational` asks for a morphism from a nonempty
  open subscheme of `𝔸ⁿ` with dense image. For an irreducible variety `X` the two agree: a
  map onto a nonempty open subset of `X` has dense image; conversely, the image of a dominant
  morphism of varieties contains a dense open subset of `X` (Chevalley's theorem), and
  restricting to its preimage gives a surjection onto it. A torus is a connected smooth
  algebraic group, hence an irreducible variety.
- **Part 3 is the second half of Proposition 12.64.** By Definition 12.62 an induced torus
  is `(𝔾_m)_{A/k}` for an étale `k`-algebra `A`. Milne's étale `k`-algebras (p.14) are the
  finite products of finite separable field extensions. Mathlib's
  `Algebra.Etale.iff_exists_algEquiv_prod` (module `Mathlib.RingTheory.Etale.Field`) says
  that a `k`-algebra of essentially finite type is formally étale exactly when it is
  isomorphic to a finite product of separable field extensions. With `Module.Finite k A`
  each factor is a finite extension. Conversely, `Algebra.Etale k A` already implies that
  `A` is finite over `k`, so the binder `[Module.Finite k A]` excludes nothing. It is kept
  because `WeilGm.groupScheme` requires it as an instance. Rationality is encoded as in
  part 1.
- **Weil restriction.** Milne's `(𝔾_m)_{B/k}` is the functor `R ↦ (B ⊗ R)ˣ` (Milne 2.55,
  p.57), which is what `WeilGm.groupScheme (CommRingCat.of k) B` represents.

## Scope

- Milne's primary definition of rationality and unirationality, through the function field
  `k(X)`, is not used. The statement uses the geometric equivalents given in
  Definition 12.59.
- The remark after Definition 12.59 (density of `X(k)` for unirational `X` over an infinite
  field) and Corollary 12.65 are not part of this statement. Proposition 12.63 is not part of
  this statement.
- Lemma 12.61 (characters of `(𝔾_m)_{k'/k}`) is not stated.

## Related Library results

- [`Torus.RationalDensity`](RationalDensity.md) proves a form of Corollary 12.65 directly,
  without unirationality.
- [`PointTopology.UnirationalTransport`](../../AlgebraicGeometry/PointTopology/UnirationalTransport.md)
  proves `HasFiniteAffineBirationalModel.isUnirational`, so parts 1 and 3 imply
  unirationality of the Weil restrictions.
- [`Torus.Induced`](Induced.md) defines `IsInducedTorus` following Kaletha–Prasad,
  Definition 2.5.1, through a Galois-permuted basis of the character lattice. Part 3 uses
  Milne's form `(𝔾_m)_{A/k}` directly and does not use `IsInducedTorus`.
- [`Torus.InducedWeilDecompositionStatement`](InducedWeilDecompositionStatement.md) states
  that a torus with `IsInducedTorus` is isomorphic to a Weil restriction
  `WeilGm.commGroupScheme k (∀ i, E i)`.
