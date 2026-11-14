# Statement: pointed maps from connected group varieties to groups of multiplicative type

Worker 75.

`Langlands.GroupScheme.MultiplicativeTypePointedMapStatement.{u} : Prop` is a
statement-only, `Prop`-valued definition. This module does not prove it, and it adds no
other definitions, theorems or axioms. It imports
[`Torus.MultiplicativeType`](MultiplicativeType.md), which gives the predicate
`IsMultiplicativeType` for group schemes over a field. Through its imports it also gives
the group schemes `GroupScheme S`, the cartesian monoidal structure on `Over S`, and
Mathlib's `Smooth` and `QuasiCompact`.

`GroupScheme S` is `Grp (Over S)`. For `G : GroupScheme S` the `S`-scheme of `G` is `G.X`.
A morphism `f : G ⟶ T` of group schemes is a homomorphism of group objects, and
`f.hom.hom : G.X ⟶ T.X` is its underlying morphism of `S`-schemes. The scoped notation of
`CategoryTheory.MonObj` is open, so `η[G.X] : 𝟙_ (Over S) ⟶ G.X` is the identity section
of `G`. Here `𝟙_ (Over S)` is the terminal object, `S` over itself.

## Lean statement

```lean
def MultiplicativeTypePointedMapStatement : Prop :=
  ∀ (k : Type u) [Field k] (G T : GroupScheme (Spec (CommRingCat.of k))),
    Smooth G.X.hom → QuasiCompact G.X.hom → ConnectedSpace G.X.left →
    IsMultiplicativeType T →
    ∀ φ : G.X ⟶ T.X, η[G.X] ≫ φ = η[T.X] →
      ∃ f : G ⟶ T, f.hom.hom = φ
```

## Objects and predicates used

- **Connected group variety.** `G` is a group scheme over `Spec k` with
  `Smooth G.X.hom` (smooth, hence locally of finite type, over `k`),
  `QuasiCompact G.X.hom` (together with smoothness: of finite type over `k`) and
  `ConnectedSpace G.X.left` (the underlying space of `G` is connected and nonempty).
- `IsMultiplicativeType T` (module [`Torus.MultiplicativeType`](MultiplicativeType.md)):
  there are a field extension `K` of `k` and a finitely generated abelian group `Λ` with
  `T_K` isomorphic to the diagonalizable group `D_K(Λ)`. This is Milne's Definition 12.17
  of an algebraic group of multiplicative type.
- **The map.** `φ : G.X ⟶ T.X` is a morphism of `k`-schemes, not assumed to respect the
  group laws. The hypothesis `η[G.X] ≫ φ = η[T.X]` says that `φ` sends the identity of
  `G` to the identity of `T`.

## Statement and quantifiers

Let `k : Type u` be a field. Let `G` be a group scheme over `Spec k` that is smooth and
quasi-compact over `k` with connected underlying space, and let `T` be a group scheme of
multiplicative type over `k`. Let `φ : G → T` be a morphism of `k`-schemes with
`φ(e) = e`. Then there is a homomorphism of group schemes `f : G ⟶ T` whose underlying
morphism of schemes is `φ`.

Equivalently, `φ` respects the group laws. The homomorphism `f` is unique, since a
homomorphism of group objects is determined by its underlying morphism.

## Source

James S. Milne, *Algebraic Groups: The theory of group schemes of finite type over a field*
(Cambridge University Press, 2017), source ID `milne-2017-algebraic-groups`, file
`Milne--Algebraic groups, the theory of group schemes of finite type over a field
(book)--2017.pdf`. Page numbers are printed page numbers; the PDF page is the printed page
plus 16.

- Proposition 12.49, p.247: "Let G be a connected group variety, and let T be a group of
  multiplicative type. Every regular map φ: G → T such that φ(e) = e is a homomorphism of
  algebraic groups."
- Chapter 1, p.6: "When G is a variety, we call (G, m) a group variety". Proposition 1.22,
  p.12: "Algebraic groups are separated (as algebraic schemes)", followed by
  "Therefore 'group variety' = 'geometrically reduced algebraic group'." Proposition 1.26
  and the sentence after it, p.13: "Therefore 'group variety' = 'smooth algebraic group'."
- Notations, p.3: "An algebraic scheme over k (or algebraic k-scheme) is a scheme of
  finite type over k." Chapter 1, p.6: "an algebraic group over k is a group object in the
  category of algebraic schemes over k."
- Definition 12.17, p.236: "An algebraic group over k is of multiplicative type if it
  becomes diagonalizable over some field containing k."

The official errata snapshot of 2026-11-02 (source ID
`milne-2017-algebraic-groups-errata-2026-11-02`) lists corrections only to 12.41 and 12.57
in Chapter 12. It has no correction to 12.49.

Milne's proof reduces to `k` algebraically closed and `T = 𝔾_m`. Proposition 12.48
writes `φ ∘ m = φ₁ · φ₂`, and evaluating at `e` gives `φ₁ = φ = φ₂`. This is explanation
only.

## Derivation from the source

- **Connected group variety `G`.** By Proposition 1.26 and the sentence after it, a group
  variety is a smooth algebraic group. An algebraic group is a group scheme of finite type
  over `k`. Smoothness over `k` gives local finite type, and with `QuasiCompact G.X.hom`
  the scheme is of finite type. Separatedness, part of Milne's notion of variety, is
  automatic for algebraic groups (Proposition 1.22), so it is not assumed. Connected is
  `ConnectedSpace G.X.left`.
- **Group of multiplicative type `T`.** This is `IsMultiplicativeType T`, the Library's
  formalization of Definition 12.17. It includes finite generation of the character group,
  so `T` is of finite type over `k`.
- **Regular map with `φ(e) = e`.** A regular map of algebraic schemes over `k` is a
  morphism of `k`-schemes, here `φ : G.X ⟶ T.X` in `Over (Spec k)`. The identity `e` of
  `G` is the `k`-point `η[G.X]`, so `φ(e) = e` is `η[G.X] ≫ φ = η[T.X]`.
- **"`φ` is a homomorphism of algebraic groups".** This is the existence of a morphism
  `f : G ⟶ T` of group objects with underlying morphism `φ`.

## Scope

- The statement is the proposition as stated, over an arbitrary field `k`.
- Remark 12.50 and Proposition 12.48 are not part of this statement.

## Related Library results

- [`Torus.PointedMorphismDescent`](PointedMorphismDescent.md) proves the case where the
  source is also a torus: `IsTorus.homOfPointedMorphism` builds a homomorphism of group
  schemes from a pointed morphism between two tori over a field. It does not cover a
  general connected group variety as source.
- [`Torus.PointedMorphism`](PointedMorphism.md) proves the same for split tori.
