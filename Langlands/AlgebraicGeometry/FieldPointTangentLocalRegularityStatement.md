# Tangent space and local cotangent space at a rational point over a field

Author: Worker 207.

`Langlands.Scheme.FieldPointTangentLocalRegularityStatement.{u}` is the
following `Prop`-valued definition:

```lean
∀ (k : Type u) [Field k]
  (X : Over (Spec (CommRingCat.of k)))
  (e : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ X),
  LocallyOfFiniteType X.hom →
    let x := e.left (IsLocalRing.closedPoint k)
    let R := X.left.presheaf.stalk x
    let T := Langlands.Scheme.tangentSpaceAtPoint X e
    FiniteDimensional k T ∧
      Module.finrank k T = Module.finrank (IsLocalRing.ResidueField R)
        (IsLocalRing.CotangentSpace R) ∧
      ∀ g : ℕ, Module.finrank k T ≤ g →
        (g : WithBot ℕ∞) ≤ ringKrullDim R → IsRegularLocalRing R
```

In words: let `X` be a scheme locally of finite type over a field `k`, and let
`x` be the `k`-rational point of `X` given by a section `e`. Let `R = O_{X,x}`
be the local ring of `X` at `x`, and let `T` be the tangent module at `e`
defined in `Langlands.AlgebraicGeometry.PointTangentSpace`. Then:

1. `T` is a finite-dimensional `k`-vector space;
2. `dim_k T` equals the dimension of the cotangent space `m_R/m_R^2` of `R`
   over the residue field `R/m_R`;
3. for every natural number `g`, if `dim_k T ≤ g` and `g ≤ dim R` (Krull
   dimension), then `R` is a regular local ring.

This file is a statement target only. It proves none of these assertions,
and it supplies no identification between `T`, a stalk or a cotangent space.
A separate proof task will prove the statement.

## The objects

Everything is in the arbitrary universe `u`.

- `k : Type u` is an arbitrary field. It need not be algebraically closed or
  perfect, and its characteristic is arbitrary.
- `X : Over (Spec (CommRingCat.of k))` is an arbitrary scheme over `Spec k`.
  Its underlying scheme is `X.left` and its structure morphism is
  `X.hom : X.left ⟶ Spec k`. There is no group structure and no smoothness,
  reducedness, connectedness, separatedness, properness or quasi-compactness
  hypothesis.
- `e : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ X` is a morphism in the slice
  category from its terminal object, that is, a section of `X.hom`: its
  underlying morphism is `e.left : Spec k ⟶ X.left`, and the slice equation
  says `e.left ≫ X.hom = 𝟙 (Spec k)`. This is a `k`-rational point of `X`.
  This is the argument shape of the published `tangentSpaceAtPoint`.
- `LocallyOfFiniteType X.hom` is Mathlib's
  `AlgebraicGeometry.LocallyOfFiniteType`, taken as an explicit hypothesis.
  It is the only hypothesis on `X`.

The three `let` bindings are abbreviations, not hypotheses.

- `x := e.left (IsLocalRing.closedPoint k)` is the image under `e.left` of the
  unique point of `Spec k`. The point `IsLocalRing.closedPoint k` is the zero
  ideal of `k`. Applying `e.left` to a point means applying its underlying
  continuous map `e.left.base`.
- `R := X.left.presheaf.stalk x` is the actual stalk of the structure sheaf of
  `X.left` at `x`, i.e. the local ring `O_{X,x}`, with Mathlib's local ring
  instance on stalks of schemes.
- `T := Langlands.Scheme.tangentSpaceAtPoint X e` is the published tangent
  module, an object of `ModuleCat (CommRingCat.of k)`. By its definition in
  `Langlands.AlgebraicGeometry.PointTangentSpace`, it is the module of global
  sections over `Spec k` of
  `tangentAtSection X e = Langlands.Scheme.Modules.dual (e* Omega_(X/k))`.
  Here `Omega_(X/k)` is the published sheaf
  `Langlands.Scheme.relativeDifferentials X.hom`, `e*` is Mathlib's pullback of
  sheaves of modules along `e.left`, and `Modules.dual` is the published
  internal Hom into the structure sheaf of `Spec k`. The `k`-module structure
  on `T` is the one of the `ModuleCat` object: Mathlib's `moduleSpecΓFunctor`
  restricts scalars along the inverse of `Scheme.ΓSpecIso`, the canonical
  isomorphism `k ≅ Γ(Spec k, O)`. The carrier of `CommRingCat.of k` is `k`
  itself, so `FiniteDimensional k T` and `Module.finrank k T` use this module
  structure. (A private elaboration check confirms that the instance found is
  `ModuleCat.isModule T`.)

No replacement tangent carrier is defined, and no identification of `T` with
another space is supplied.

## The conclusion

The conclusion is a conjunction of three assertions.

1. `FiniteDimensional k T`: `T` is finitely generated as a `k`-vector space.
2. `Module.finrank k T = Module.finrank (IsLocalRing.ResidueField R)
   (IsLocalRing.CotangentSpace R)`. On the right,
   `IsLocalRing.ResidueField R` is Mathlib's residue field `R ⧸ m_R`, and
   `IsLocalRing.CotangentSpace R` is Mathlib's cotangent space
   `(maximalIdeal R).Cotangent`, i.e. `m_R/m_R^2` with its canonical vector
   space structure over the residue field. Each side is a dimension over that
   space's own canonical field: `T` over `k`, and `m_R/m_R^2` over `R/m_R`.
   The residue field `R/m_R` is isomorphic to `k` because `x` is a rational
   point, but this isomorphism is not definitional and is not supplied as a
   premise. A proof has to construct the scalar transport and the comparison
   itself.

   Mathlib's `Module.finrank` is `0` on infinite-dimensional spaces. Item 1
   makes the left side an honest dimension. The equality alone does not
   assert that `m_R/m_R^2` is finite-dimensional; that is true here because
   `R` is Noetherian (see below), but it is not a separate conjunct.
3. `∀ g : ℕ, Module.finrank k T ≤ g → (g : WithBot ℕ∞) ≤ ringKrullDim R →
   IsRegularLocalRing R`. Here `ringKrullDim R : WithBot ℕ∞` is Mathlib's
   Krull dimension of the stalk and `g` is cast into `WithBot ℕ∞`.
   `IsRegularLocalRing R` is Mathlib's class from
   `Mathlib.RingTheory.RegularLocalRing.Defs`: `R` is local and Noetherian
   and `(maximalIdeal R).spanFinrank = ringKrullDim R`, that is, its maximal
   ideal is generated by `dim R` elements (Stacks Tag 00KU). The conclusion
   therefore includes that `R` is Noetherian.

No algebraic-closedness, smoothness or reducedness hypothesis appears, and no
hypothesis relates `g` to `X` other than the two inequalities.

## Source and derived provenance

The statement is derived. It is a specialization of two lemmas of the Stacks
Project to a rational point over a field, followed by a numerical consequence
that uses Mathlib's existing regularity criterion. No source states this
bundled Lean proposition literally.

Source: the registered retained folder
`stacks-flasque-affine-vanishing-kunneth-a04446e5` (Stacks Project LaTeX
sources at commit `a04446e57ec1fbc252a871afcec7752fb2807b14`), file
`varieties.tex` (SHA-256
`53d0af48818d22ae85675eff76b79fcad4335fda0b4574ec09f5c9e73cc93995`),
Section 33.16 "Tangent spaces" (Tag 0B28, starting at source line 2911):

- Definition 33.16.3 (Tag 0B2C, `definition-tangent-space`, lines 2987–2994)
  defines the tangent space `T_{X/S,x}` of `f : X → S` at `x` as the
  `κ(x)`-vector space of dotted arrows `Spec(κ(x)[ε]) → X` in the diagram
  `equation-tangent-space` (lines 2926–2944).
- Lemma 33.16.4 (Tag 0B2D, `lemma-tangent-space-cotangent-space`, lines
  3013–3021) gives a canonical isomorphism
  `T_{X/S,x} = Hom_{O_{X,x}}(Omega_{X/S,x}, κ(x))` of `κ(x)`-vector spaces.
- Lemma 33.16.5 (Tag 0B2E, `lemma-tangent-space-rational-point`, lines
  3058–3077, proof to line 3105) says: if `κ(x) = κ(s)` for `s = f(x)`, then
  `m_x/(m_x^2 + m_s O_{X,x}) = Omega_{X/S,x} ⊗ κ(x)` and
  `T_{X/S,x} = Hom_{κ(x)}(m_x/(m_x^2 + m_s O_{X,x}), κ(x))`.

### The specialization

Take `S = Spec k` and `x = e(Spec k)`. Then `s` is the unique point of
`Spec k`, so `κ(s) = k` and `m_s = 0`. Because `e` is a section of
`X → Spec k`, the composite `k → O_{X,x} → κ(x)` is an isomorphism, so
`κ(x) = κ(s)` and Lemma 33.16.5 applies. It gives
`Omega_{X/k,x} ⊗ κ(x) = m_x/m_x^2` and
`T_{X/k,x} = Hom_{κ(x)}(m_x/m_x^2, κ(x))`.

The Lean module `T` is not defined through dual numbers. It is
`Γ(Spec k, Hom(e* Omega_(X/k), O_{Spec k}))`. Since `Spec k` has a single
point, mathematically its global sections are the `k`-linear maps from
`Γ(Spec k, e* Omega_(X/k)) = Omega_{X/k,x} ⊗_{O_{X,x}} κ(x)` to `k`, which
are the `O_{X,x}`-linear maps `Omega_{X/k,x} → κ(x)`: the right side of
Lemma 33.16.4. Together with Lemma 33.16.5, `T` is the `k`-dual of
`m_x/m_x^2`, with `κ(x)` identified with `k`.

Local finite type of `X` over `k` makes `O_{X,x}` Noetherian: it is a
localization of a finitely generated `k`-algebra. So `m_x/m_x^2` is
finite-dimensional over `κ(x)`. Its dual `T` is then finite-dimensional, and
taking dimensions gives items 1 and 2.

### The regularity consequence

Item 3 combines item 2 with Mathlib's regularity criterion.
`IsLocalRing.spanFinrank_maximalIdeal_eq_finrank_cotangentSpace` (for a
Noetherian local ring) and `IsRegularLocalRing.iff_finrank_cotangentSpace`
(`Mathlib/RingTheory/RegularLocalRing/Defs.lean`, lines 75–77) relate the
number of generators of `m_R` to `dim (m_R/m_R^2)`. Krull's height theorem
gives `ringKrullDim R ≤ spanFinrank (m_R)`
(`ringKrullDim_le_spanFinrank_maximalIdeal`). Thus
`spanFinrank (m_R) = dim T ≤ g ≤ dim R` forces equality, and
`IsRegularLocalRing.of_spanFinrank_maximalIdeal_le` gives regularity. This
is the usual "tangent dimension at most the local dimension implies regular"
criterion, stated with an auxiliary natural number `g` (for example a
relative dimension) between the two numbers. It adds no new regularity
definition or criterion to the Library.

## Future proof obligations

The statement does not supply any of the following; a proof must build them
from the actual objects:

- the comparison between the published sheaf-theoretic `T` and
  `Hom_{O_{X,x}}(Omega_{X/k,x}, κ(x))`. This needs the global sections of the
  published internal dual on the one-point space `Spec k`, the stalk of
  Mathlib's module pullback along `e.left`, and the stalk of the published
  `relativeDifferentials` at `x` (Stacks Modules, Lemma
  `modules-lemma-stalk-module-differentials`, cited in the proof of Lemma
  33.16.5);
- the algebraic isomorphism `m_x/m_x^2 ≅ Omega_{O_{X,x}/k} ⊗ κ(x)` at a
  rational point (Lemma 33.16.5);
- the scalar transport between `k` and `IsLocalRing.ResidueField R`, needed
  to compare dimensions over the two canonical fields;
- Noetherianity of the stalk from local finite type (for example via
  Mathlib's `LocallyOfFiniteType.isLocallyNoetherian`) and the resulting
  finite-dimensionality.

A point-set or purely algebraic substitute for `T` would not prove this
statement, because `T` is fixed as the published construction.

## Imports

- `Langlands.AlgebraicGeometry.PointTangentSpace` (published, unchanged):
  `Langlands.Scheme.tangentSpaceAtPoint`;
- `Mathlib.AlgebraicGeometry.Morphisms.FiniteType`: `LocallyOfFiniteType`;
- `Mathlib.LinearAlgebra.FiniteDimensional.Defs`: `FiniteDimensional`,
  `Module.finrank`;
- `Mathlib.RingTheory.RegularLocalRing.Defs`: `IsRegularLocalRing`, together
  with `IsLocalRing.ResidueField`, `IsLocalRing.CotangentSpace` and
  `ringKrullDim` through its imports.

No existing Lean or Markdown file is changed.

## Verification

`lean_check` in environment `3b864ddf-f0af-4c18-8903-c6f813a0ce0f` compiles
`Langlands.AlgebraicGeometry.FieldPointTangentLocalRegularityStatement` with no
errors or warnings. Inspection of the declaration reports a definition with
the single universe parameter `u`, `statement_returns_prop: true`, and only
the standard axioms `propext`, `Classical.choice` and `Quot.sound`. The file
contains no `sorry`, `admit` or new axiom.
