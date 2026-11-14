# Statement: invertible functions on a product of irreducible varieties

Worker 75.

`Langlands.GroupScheme.UnitsProductDecompositionStatement.{u} : Prop` is a statement-only,
`Prop`-valued definition. This module does not prove it, and it adds no other definitions,
theorems or axioms. It imports [`Multiplicative`](../Multiplicative.md), which gives the
multiplicative group scheme `Gm S`. Through its imports it also gives the cartesian
monoidal structure on `Over S`. It also imports
`Mathlib.AlgebraicGeometry.Morphisms.FiniteType` (`LocallyOfFiniteType`),
`Mathlib.AlgebraicGeometry.Morphisms.Separated` (`IsSeparated`) and
`Mathlib.FieldTheory.IsAlgClosed.Basic` (`IsAlgClosed`). `QuasiCompact` and `IsReduced`
are also from Mathlib.

`Gm S : CommGroupScheme S` is the multiplicative group over `S`, and `(Gm S).X` is its
`S`-scheme. For an `S`-scheme `T`, a morphism `T ⟶ (Gm S).X` is the same as a global
unit of `T` (`Gm.pointsEquiv`, an isomorphism of groups). The scoped notation of
`CategoryTheory.MonObj` is open. So for every `S`-scheme `T` the set of morphisms
`T ⟶ (Gm S).X` has the group structure induced by the group law of `Gm S`, and under
`Gm.pointsEquiv` the product `a * b` is the product of the corresponding units.

The category `Over S` carries Mathlib's cartesian monoidal structure. Here `X ⊗ Y` is the
fibre product `X ×_S Y`, and `fst X Y : X ⊗ Y ⟶ X` and `snd X Y : X ⊗ Y ⟶ Y` are the two
projections.

## Lean statement

```lean
def UnitsProductDecompositionStatement : Prop :=
  ∀ (k : Type u) [Field k] [IsAlgClosed k] (X Y : Over (Spec (CommRingCat.of k))),
    LocallyOfFiniteType X.hom → QuasiCompact X.hom → IsSeparated X.hom →
      IsReduced X.left → IrreducibleSpace X.left →
    LocallyOfFiniteType Y.hom → QuasiCompact Y.hom → IsSeparated Y.hom →
      IsReduced Y.left → IrreducibleSpace Y.left →
    ∀ u : X ⊗ Y ⟶ (Gm (Spec (CommRingCat.of k))).X,
      ∃ (u₁ : X ⟶ (Gm (Spec (CommRingCat.of k))).X) (u₂ : Y ⟶ (Gm (Spec (CommRingCat.of k))).X),
        u = (fst X Y ≫ u₁) * (snd X Y ≫ u₂)
```

## Objects and predicates used

- **Irreducible algebraic variety over an algebraically closed field.** `k` is a field
  with `IsAlgClosed k`. `X` is a scheme over `Spec k` with `LocallyOfFiniteType X.hom` and
  `QuasiCompact X.hom` (together: of finite type over `k`), `IsSeparated X.hom`
  (separated over `k`), `IsReduced X.left` (reduced) and `IrreducibleSpace X.left` (the
  underlying space is irreducible, in particular nonempty). `Y` satisfies the same
  hypotheses.
- **The function `u`.** `u : X ⊗ Y ⟶ (Gm (Spec k)).X` is a morphism of `k`-schemes from
  `X ×_k Y` to `𝔾_m`, that is, an invertible function on `X ×_k Y`.
- **The product `u₁ · u₂`.** For `u₁ : X ⟶ 𝔾_m` and `u₂ : Y ⟶ 𝔾_m`, the morphisms
  `fst X Y ≫ u₁` and `snd X Y ≫ u₂` are the functions `(x, y) ↦ u₁(x)` and
  `(x, y) ↦ u₂(y)` on `X ×_k Y`. Their product `*` in the group of morphisms
  `X ⊗ Y ⟶ (Gm (Spec k)).X` is the function `(x, y) ↦ u₁(x) u₂(y)`.

## Statement and quantifiers

Let `k : Type u` be an algebraically closed field. Let `X` and `Y` be schemes over
`Spec k` that are of finite type, separated, reduced and irreducible. Let
`u : X ×_k Y → 𝔾_m` be a morphism of `k`-schemes. Then there are morphisms of `k`-schemes
`u₁ : X → 𝔾_m` and `u₂ : Y → 𝔾_m` with

`u = (u₁ ∘ pr₁) · (u₂ ∘ pr₂)`,

that is, `u(x, y) = u₁(x) u₂(y)`.

All schemes are in universe `u`.

## Source

James S. Milne, *Algebraic Groups: The theory of group schemes of finite type over a field*
(Cambridge University Press, 2017), source ID `milne-2017-algebraic-groups`, file
`Milne--Algebraic groups, the theory of group schemes of finite type over a field
(book)--2017.pdf`. Page numbers are printed page numbers; the PDF page is the printed page
plus 16.

- Proposition 12.48, p.246: "Let X and Y be irreducible algebraic varieties over an
  algebraically closed field k. Every regular map u: X × Y → G_m is of the form
  u = u₁ · u₂ with u₁ (resp. u₂) a regular map X → G_m (resp. Y → G_m)."
- Notations, p.3: "An algebraic scheme over k (or algebraic k-scheme) is a scheme of
  finite type over k. An algebraic scheme is an algebraic variety if it is geometrically
  reduced and separated." Also: "Unadorned products of algebraic k-schemes are over k."
- A.43, p.576: "If k is perfect, then every reduced algebraic scheme over k is
  geometrically reduced." A.44, p.576: "An algebraic variety over k is an algebraic scheme
  over k that is both separated and geometrically reduced."

The official errata snapshot of 2026-11-02 (source ID
`milne-2017-algebraic-groups-errata-2026-11-02`) lists corrections only to 12.41 and 12.57
in Chapter 12. It has no correction to 12.48.

Milne's proof, p.247, chooses normal points `x₀` of `X` and `y₀` of `Y` and compares `u`
with `v(x, y) = u(x, y₀) u(x₀, y) u(x₀, y₀)⁻¹`. After shrinking to affine normal
neighbourhoods, he embeds `X` and `Y` as dense opens of normal projective varieties and
shows that the divisor of `u/v` is zero, so `u/v` is a constant, equal to `1`. This is
explanation only.

## Derivation from the source

- **Algebraic variety.** An algebraic variety is a scheme of finite type over `k`
  (`LocallyOfFiniteType X.hom` and `QuasiCompact X.hom`) that is separated
  (`IsSeparated X.hom`) and geometrically reduced. Since `k` is algebraically closed, it
  is perfect, and by A.43 a reduced algebraic scheme over `k` is geometrically reduced.
  The converse holds because `X_{k^a} = X` here. So geometrically reduced is
  `IsReduced X.left`.
- **Irreducible.** Milne's `|X|` is the space of closed points of `X`. For a scheme of
  finite type over a field, the closed points are dense in every closed subset, so `|X|`
  is irreducible exactly when the whole underlying space is. This is
  `IrreducibleSpace X.left`.
- **Regular maps and `𝔾_m`.** A regular map is a morphism of algebraic schemes over `k`,
  that is, a morphism in `Over (Spec k)`. Milne's `𝔾_m` over `k` is the Library's
  `Gm (Spec k)`. The product `X × Y` is over `k`, so it is `X ⊗ Y` in `Over (Spec k)`.
- **`u = u₁ · u₂`.** Here `u₁ · u₂` is the function `(x, y) ↦ u₁(x) u₂(y)` on `X × Y`.
  This is the product, in the group of morphisms `X ⊗ Y ⟶ 𝔾_m`, of `u₁` and `u₂`
  composed with the projections.

## Scope

- The statement is the proposition as stated, over an algebraically closed field.
- Remark 12.50 (the isomorphism `U(X) ⊕ U(Y) ≅ U(X × Y)` with
  `U(X) = Γ(X, 𝒪_X)ˣ / kˣ`, and its extension to more general fields) is not stated.
- Proposition 12.49, which Milne deduces from Proposition 12.48, is not part of this
  statement.

## Related Library results

- [`Multiplicative`](../Multiplicative.md) defines `Gm S` and proves that its `T`-points
  are the global units of `T` (`Gm.pointsEquiv`).
