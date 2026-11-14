# Statement: rigidity of families of homomorphisms between diagonalizable groups

Worker 75.

`Langlands.GroupScheme.DiagonalizableRigidityStatement.{u} : Prop` is a statement-only,
`Prop`-valued definition. This module does not prove it, and it adds no other definitions,
theorems or axioms. It imports [`Torus.Diagonalizable`](Diagonalizable.md), which gives the
diagonalizable group scheme `Diagonalizable.groupScheme R Λ`. Through its imports it also
gives the group schemes `GroupScheme S` and the cartesian monoidal structure on `Over S`.
It also imports `Mathlib.AlgebraicGeometry.Morphisms.FiniteType` for
`LocallyOfFiniteType`. `QuasiCompact` is also from Mathlib.

`GroupScheme S` is `Grp (Over S)`. For `G : GroupScheme S` the `S`-scheme of `G` is `G.X`.
The scoped notation of `CategoryTheory.MonObj` is open. So for every `S`-scheme `T` the
set of morphisms `T ⟶ G.X` (the group `G(T)` of `T`-points of `G`) has the group
structure induced by the group law of `G`. In this group, `g * g'` is the product.

The category `Over S` carries Mathlib's cartesian monoidal structure. Here `X ⊗ G.X` is
the fibre product `X ×_S G.X`, and `𝟙_ (Over S)` is the terminal object, `S` over itself.
For `x : T ⟶ X` and `g : T ⟶ G.X`, `lift x g : T ⟶ X ⊗ G.X` is the `T`-point `(x, g)` of
the product. `toUnit T : T ⟶ 𝟙_ (Over S)` is the unique morphism to the terminal object.

## Lean statement

```lean
def DiagonalizableRigidityStatement : Prop :=
  ∀ (k : Type u) [Field k] (G H : GroupScheme (Spec (CommRingCat.of k)))
    (Λ Λ' : Type u) [AddCommGroup Λ] [AddCommGroup Λ'], AddGroup.FG Λ → AddGroup.FG Λ' →
    Nonempty (G ≅ (Diagonalizable.groupScheme (CommRingCat.of k) Λ).toGrp) →
    Nonempty (H ≅ (Diagonalizable.groupScheme (CommRingCat.of k) Λ').toGrp) →
    ∀ (X : Over (Spec (CommRingCat.of k))), LocallyOfFiniteType X.hom → QuasiCompact X.hom →
      ConnectedSpace X.left →
      ∀ φ : X ⊗ G.X ⟶ H.X,
        (∀ (T : Over (Spec (CommRingCat.of k))) (x : T ⟶ X) (g g' : T ⟶ G.X),
          lift x (g * g') ≫ φ = (lift x g ≫ φ) * (lift x g' ≫ φ)) →
        ∀ (x₀ : 𝟙_ (Over (Spec (CommRingCat.of k))) ⟶ X)
          (T : Over (Spec (CommRingCat.of k))) (x : T ⟶ X) (g : T ⟶ G.X),
          lift x g ≫ φ = lift (toUnit T ≫ x₀) g ≫ φ
```

## Objects and predicates used

- `Diagonalizable.groupScheme (CommRingCat.of k) Λ` (module
  [`Torus.Diagonalizable`](Diagonalizable.md)) is the diagonalizable group scheme
  `D(Λ) = Spec k[Λ]` over `Spec k`, a commutative group scheme. `.toGrp` is its
  underlying group scheme. Its `T`-points are the characters `Λ → Γ(T, 𝒪_T)ˣ`.
- **Diagonalizable algebraic groups.** `G` is given with a finitely generated abelian group
  `Λ : Type u` (`AddGroup.FG Λ`) and an isomorphism of group schemes `G ≅ D(Λ)`, given
  only as `Nonempty`. `H` is given in the same way with `Λ'`.
- **Connected algebraic scheme.** `X` is a scheme over `Spec k` with
  `LocallyOfFiniteType X.hom` and `QuasiCompact X.hom` (together: of finite type over `k`)
  and `ConnectedSpace X.left` (the underlying space of `X` is connected and nonempty).
- **The family.** `φ : X ⊗ G.X ⟶ H.X` is a morphism of `k`-schemes from `X ×_k G` to `H`.
  For a `T`-point `x` of `X` and a `T`-point `g` of `G`, the `T`-point `φ(x, g)` of `H` is
  `lift x g ≫ φ`.
- **`k`-points.** A `k`-point of `X` is a morphism `x₀ : 𝟙_ (Over (Spec k)) ⟶ X` of
  `k`-schemes from `Spec k` to `X`. Over a test scheme `T` it gives the constant `T`-point
  `toUnit T ≫ x₀`.

## Statement and quantifiers

Let `k : Type u` be a field, and let `G` and `H` be group schemes over `Spec k`. Let `Λ`
and `Λ'` be finitely generated abelian groups in `Type u` with `G ≅ D(Λ)` and
`H ≅ D(Λ')`. Let `X` be a scheme of finite type over `k` with connected underlying space.
Let `φ : X ×_k G → H` be a morphism of `k`-schemes. Assume that for every `k`-scheme `T`,
every `x : T ⟶ X` and all `g, g' : T ⟶ G.X`,

`φ(x, g * g') = φ(x, g) * φ(x, g')`.

Then for every `k`-point `x₀` of `X`, every `k`-scheme `T`, every `x : T ⟶ X` and every
`g : T ⟶ G.X`,

`φ(x, g) = φ(x₀, g)`,

where on the right `x₀` is viewed as the constant `T`-point `toUnit T ≫ x₀`.

All schemes, including the test schemes `T`, are in universe `u`.

## Source

James S. Milne, *Algebraic Groups: The theory of group schemes of finite type over a field*
(Cambridge University Press, 2017), source ID `milne-2017-algebraic-groups`, file
`Milne--Algebraic groups, the theory of group schemes of finite type over a field
(book)--2017.pdf`. Page numbers are printed page numbers; the PDF page is the printed page
plus 16.

- Theorem 12.36, p.243: "Let G and H be diagonalizable groups over k, and let X be a
  connected algebraic scheme over k. Let φ: X × G → H be a morphism such that, for all
  k-algebras R and x ∈ X(R), the map g ↦ φ(x, g): G(R) → H(R) is a homomorphism. For any
  x₀ ∈ X(k), we have φ(x, g) = φ(x₀, g) for all k-algebras R and (x, g) ∈ X(R) × G(R)."
  The sentence before it reads: "The next theorem says that diagonalizable groups are
  rigid in the sense that a family of homomorphisms from one to a second parameterized by
  a connected algebraic scheme is constant."
- Definition 12.7 and Theorem 12.8, p.233: "An algebraic group G is diagonalizable if the
  group-like elements in O(G) span it as a k-vector space." "An algebraic group G is
  diagonalizable if and only if it is isomorphic to D(M) for some commutative group M."
  Theorem 12.9(a), p.233: "The functor M ⇝ D(M) is a contravariant equivalence from the
  category of finitely generated commutative groups to the category of diagonalizable
  algebraic groups."
- Notations, p.3: "An algebraic scheme over k (or algebraic k-scheme) is a scheme of
  finite type over k." Chapter 1, p.6: "an algebraic group over k is a group object in the
  category of algebraic schemes over k."

The official errata snapshot of 2026-11-02 (source ID
`milne-2017-algebraic-groups-errata-2026-11-02`) lists corrections only to 12.41 and 12.57
in Chapter 12. It has no correction to 12.36.

Milne's proof first treats finite `G`, where `φ` gives a morphism from `X` to the étale
scheme `Hom(G, H)` (Lemma 12.35). In general he reduces to `k` algebraically closed and `X`
affine, applies the finite case to every `G_n`, and concludes with the density theorem
12.33. This is explanation only.

## Derivation from the source

- **Diagonalizable groups.** Milne's `G` and `H` are diagonalizable algebraic groups over
  `k`. By Theorems 12.8 and 12.9(a) these are the algebraic groups isomorphic to `D(M)`
  for a finitely generated commutative group `M`. Finite generation is forced because
  algebraic groups are of finite type over `k`. Here this is
  `Nonempty (G ≅ D_k(Λ))` with `AddGroup.FG Λ`, and the same for `H`.
- **Connected algebraic scheme `X`.** Algebraic means of finite type over `k`, that is,
  `LocallyOfFiniteType X.hom` and `QuasiCompact X.hom`. Connected is
  `ConnectedSpace X.left`.
- **The morphism `φ : X × G → H`.** Products of `k`-schemes are fibre products over
  `Spec k`, which is the monoidal product `X ⊗ G.X` in `Over (Spec k)`. The value
  `φ(x, g)` at points is `lift x g ≫ φ`.
- **Points over `k`-algebras versus all `k`-schemes.** Milne tests the hypothesis and the
  conclusion on `R`-points for `k`-algebras `R`. Here both are tested on `T`-points for
  every `k`-scheme `T` in universe `u`. The two are equivalent. The affine schemes
  `Spec R` are among the `T`. Conversely, both sides of each equation are morphisms
  `T ⟶ H.X`, and equality of morphisms can be checked on an affine open cover of `T`. The
  same holds if Milne's `R` ranges only over finitely generated `k`-algebras. Since
  `X ×_k G` and `X ×_k G ×_k G` are of finite type, the equations at their own universal
  points imply all others, and those are checked on affine opens with finitely generated
  coordinate rings.
- **"`g ↦ φ(x, g)` is a homomorphism".** Over each `T`, the map `G(T) → H(T)` respects
  products: `lift x (g * g') ≫ φ = (lift x g ≫ φ) * (lift x g' ≫ φ)`. Units and inverses
  are then respected automatically, since a multiplicative map between groups is a group
  homomorphism.
- **`x₀ ∈ X(k)` and `φ(x₀, g)`.** A `k`-point is a morphism from `Spec k`, the terminal
  object `𝟙_ (Over (Spec k))`, to `X`. For `g ∈ G(T)`, Milne's `φ(x₀, g)` uses the image
  of `x₀` in `X(T)`, which is `toUnit T ≫ x₀`.

## Scope

- The statement is for diagonalizable groups, as in the source. It does not state the
  version for groups of multiplicative type, which Milne uses after extending the base
  field in the proof of Corollary 12.37.
- The morphism `X → Hom(G, H)` of Milne's proof and the scheme `Hom(G, H)` of Lemma 12.35
  are not formalized.

## Related Library results

- [`Torus.HomFamilyRigidity`](HomFamilyRigidity.md) proves a version for split tori `G`
  and `H` over any base scheme and any connected parameter scheme. There the family is
  given as a natural family of homomorphisms on points rather than as a morphism
  `X ×_k G → H`. It is internal infrastructure and does not state Theorem 12.36.
- [`Rational.TorusNormalizerRigidity`](../Rational/TorusNormalizerRigidity.md) proves the
  corresponding rigidity for conjugation families of a split torus.
- [`Torus.Diagonalizable`](Diagonalizable.md) defines `D(Λ)`.
