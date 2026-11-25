# Statement: every torus is a quotient of an induced torus

`Langlands.GroupScheme.InducedTorusQuotientStatement.{u} : Prop` is a statement-only,
`Prop`-valued definition. This module does not prove it, and it adds no other definitions,
theorems or axioms. It imports:

- [`Torus.WeilRestrictionCommutative`](WeilRestrictionCommutative.md). Through it, this
  module gets the Weil restriction `WeilGm.groupScheme A B` of the multiplicative group
  (module [`Torus.WeilRestriction`](WeilRestriction.md)) and the predicate `IsTorus` over a
  field (module [`Torus.Lattice`](Lattice.md)).
- Mathlib's `Mathlib.AlgebraicGeometry.Morphisms.Flat`, for `Flat`, and
  `Mathlib.RingTheory.Etale.Basic`, for `Algebra.Etale`.

## Lean statement

```lean
def InducedTorusQuotientStatement : Prop :=
  ∀ (k : Type u) [Field k] (T : GroupScheme (Spec (CommRingCat.of k))), IsTorus T →
    ∃ (A : Type u) (_ : CommRing A) (_ : Algebra k A) (_ : Algebra.Etale k A)
      (_ : Module.Finite k A) (q : WeilGm.groupScheme (CommRingCat.of k) A ⟶ T),
      Flat q.hom.hom.left ∧ Surjective q.hom.hom.left
```

## Objects and predicates used

- **Group schemes.** `GroupScheme S` is `Grp (Over S)`. A morphism `q : G ⟶ T` of group
  schemes is a homomorphism of group objects. `q.hom.hom : G.X ⟶ T.X` is its underlying
  morphism in `Over S`, and `q.hom.hom.left` is the underlying morphism of schemes.
- `IsTorus T`: there is a field extension `K` of `k` such that the base change `T_K` is a
  split torus, that is, isomorphic to `𝔾_m^I` over `K` for a finite type `I` (Milne's
  Definition 12.14).
- **Weil restriction of `𝔾_m`.** For a commutative `k`-algebra `A` that is finite and
  projective as a `k`-module, `WeilGm.groupScheme (CommRingCat.of k) A` is a group scheme
  over `Spec k`. Its points over a test scheme `U` are the units of `A ⊗[k] Γ(U)`
  (`WeilGm.pointsEquiv`). This is Milne's `(𝔾_m)_{A/k}`. Every `k`-module is projective, so
  over a field only `Module.Finite k A` is assumed.
- **Étale algebras.** `Algebra.Etale k A` is Mathlib's étale algebra (formally étale and of
  finite presentation). With `Module.Finite k A` this is Milne's étale `k`-algebra, a finite
  product of finite separable field extensions of `k` (see Derivation below).
- `Flat` and `Surjective` are Mathlib's morphism properties of schemes.

## Statement and quantifiers

Let `k : Type u` be a field and `T` a torus over `k`. Then there are a commutative
`k`-algebra `A : Type u` that is étale and finite over `k`, and a homomorphism of group
schemes `q : (𝔾_m)_{A/k} ⟶ T` whose underlying morphism of schemes is flat and surjective.

The algebra `A`, its ring and algebra structures, and the instance arguments
`Algebra.Etale k A` and `Module.Finite k A` are all existentially quantified, as is `q`.

## Source

James S. Milne, *Algebraic Groups: The theory of group schemes of finite type over a field*
(Cambridge University Press, 2017), source ID `milne-2017-algebraic-groups`, file
`Milne--Algebraic groups, the theory of group schemes of finite type over a field
(book)--2017.pdf`. Page numbers are printed page numbers; the PDF page is the printed page
plus 16.

- Proposition 12.63, p.251: "Every torus T is a quotient of an induced torus."
- Definition 12.62, p.251: "A torus is said to be induced (or quasi-split or quasi-trivial)
  if it is of the form (𝔾_m)_{A/k} for an étale k-algebra A."
- Definition 5.5, p.99: "A homomorphism of algebraic groups is a quotient map if it is
  faithfully flat. Thus a homomorphism is a quotient map if it is both flat and surjective."
- p.14: "An étale k-algebra is a finite product of finite separable field extensions of k."
- Definition 12.14, p.236 (tori), as formalized by `IsTorus`.
- Lemma 12.61, p.251 (characters of `(𝔾_m)_{k'/k}`), used only in the proof outline below.

The official errata snapshot of 2026-11-02 (source ID
`milne-2017-algebraic-groups-errata-2026-11-02`) lists corrections only to 12.41 and 12.57
in Chapter 12. It has no correction to 12.62 or 12.63.

Milne's proof, in outline (explanation only): let `Γ = Gal(kˢ/k)`. Every finitely generated
continuous `Γ`-module `M` is the image of a surjection `⊕ᵢ ℤ[Γ/Δᵢ] → M` from a finite sum of
permutation modules, with open subgroups `Δᵢ` of `Γ` (the stabilizers of a finite generating
set). Milne applies this to the dual `X*(T)^∨` of the character module of `T`, and then
dualizes. The dual of `ℤ[Γ/Δᵢ]` has the same form, so dualizing gives an injective
homomorphism of `Γ`-modules `X*(T) → ⊕ᵢ ℤ[Γ/Δᵢ]` (his equation (81)). With
`kᵢ = (kˢ)^{Δᵢ}`, Lemma 12.61 identifies `ℤ[Γ/Δᵢ]` with `X*((𝔾_m)_{kᵢ/k})`, and the injection
on character modules corresponds to a surjective homomorphism of tori
`∏ᵢ (𝔾_m)_{kᵢ/k} → T`.

## Derivation from the source

- **Torus `T`.** This is `IsTorus T`, the Library's formalization of Definition 12.14.
- **Induced torus.** By Definition 12.62 an induced torus is `(𝔾_m)_{A/k}` for an étale
  `k`-algebra `A`, here `WeilGm.groupScheme (CommRingCat.of k) A`. Milne's étale
  `k`-algebras (p.14) are the finite products of finite separable field extensions.
  Mathlib's `Algebra.Etale.iff_exists_algEquiv_prod` (module `Mathlib.RingTheory.Etale.Field`)
  says that `Algebra.Etale k A` holds exactly when `A` is isomorphic as a `k`-algebra to a
  finite product of fields, each finite and separable over `k`. So `Algebra.Etale k A` is
  Milne's notion. (The same module also has the different lemma
  `Algebra.FormallyEtale.iff_exists_algEquiv_prod`, about formally étale algebras of
  essentially finite type; it is not used here.) A finite product of finite field extensions
  is finite over `k`, so `Algebra.Etale k A` already implies `Module.Finite k A`, and the
  binder `Module.Finite k A` excludes nothing. It is needed because `WeilGm.groupScheme`
  requires it as an instance.
- **Quotient.** "`T` is a quotient of `G`" means that there is a quotient map `G → T`. By
  Definition 5.5 this is a homomorphism of algebraic groups that is faithfully flat, that is,
  flat and surjective. Here it is a homomorphism `q` of group schemes over `Spec k` with
  `Flat q.hom.hom.left` and `Surjective q.hom.hom.left`.
- **Weil restriction.** Milne's `(𝔾_m)_{A/k}` is the functor `R ↦ (A ⊗ R)ˣ` (Milne 2.55,
  p.57), which is what `WeilGm.groupScheme (CommRingCat.of k) A` represents.

## Scope

- The statement is the proposition as stated, over an arbitrary field `k`. It does not
  prescribe a finite Galois splitting extension `L/k` of `T`. Milne's proof builds `A` as a
  finite product `∏ᵢ kᵢ` of fixed fields `kᵢ = (kˢ)^{Δᵢ}`. If `T` splits over `L`, these
  can be taken to be intermediate fields of `L/k`. So the factors `kᵢ` lie inside `L`, but
  `A` itself is a product of fields and in general is not a subalgebra of any single field.
  For example, let `k` be algebraically closed and `T = 𝔾_m²`, which splits over `L = k`.
  The only `k`-subalgebra of `k` is `k`, and `𝔾_m → 𝔾_m²` is never surjective, since it
  would give an injection `ℤ² → ℤ` of character groups. The choice `A = k × k` works.
- Lemma 12.61 (characters of `(𝔾_m)_{k'/k}`) and Proposition 12.64 are not part of this
  statement.

## Related Library results

- [`Torus.InducedEmbedding`](InducedEmbedding.md) proves a companion result in the other
  direction: `IsTorus.exists_mono_inducedTorus` gives a homomorphism from a torus to an
  induced torus (in the sense of `IsInducedTorus`) whose underlying morphism is a
  monomorphism.
- [`Torus.Induced`](Induced.md) defines `IsInducedTorus` following Kaletha–Prasad,
  Definition 2.5.1, through a Galois-permuted basis of the character lattice. This statement
  uses Milne's form `(𝔾_m)_{A/k}` directly and does not use `IsInducedTorus`.
- [`Torus.InducedWeilDecompositionStatement`](InducedWeilDecompositionStatement.md) states
  that a torus with `IsInducedTorus` is isomorphic to a Weil restriction
  `WeilGm.commGroupScheme k (∀ i, E i)`.
