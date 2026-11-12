# Gluing along commuting squares for category-valued pseudofunctors

This module is internal. It sets up gluing of objects, morphisms and actual
points of a pseudofunctor along one commuting square of test objects. It then
proves the lifting step in the proof of Stacks Lemma 90.13.2 (Tag 06IU), in a
form that does not use deformation categories. All declarations are in the
namespace `Langlands.CategoryTheory.PseudofunctorSquareGluing`.

Throughout, `C` is a category and `F : LocallyDiscrete Cᵒᵖ ⥤ᵖ Cat` is a
pseudofunctor. For `f : Y ⟶ X` and an object `M` of `F` over `X`, write
`f^* M` for `(F.map f.op.toLoc).toFunctor.obj M`. Write `m(f, g, gf)` for the
composition comparison `F.mapComp' f g gf : (gf)^* ≅ g^* ∘ f^*`, where
`g ≫ f = gf`. The relation `g ≫ f = gf` is turned into the equation needed by
`mapComp'` by `toLoc_comp`.

## Coherence lemmas

- `mapComp'_hom_app_map_inv_app` and `map_hom_app_mapComp'_inv_app` are the
  associativity coherence of the composition comparisons, evaluated at an
  object. They are rearrangements of Mathlib's
  `Pseudofunctor.mapComp'₀₂₃_inv_comp_mapComp'₀₁₃_hom_app`.
- `pullHom_conj`: if `φ : a₁^* M ⟶ a₁'^* M'` with `j ≫ a = a₁` and
  `j ≫ a' = a₁'`, then the Mathlib `pullHom` along `i` of the conjugate
  `m(a, j, a₁)⁻¹ ≫ φ ≫ m(a', j, a₁')` is the conjugate of `pullHom φ i` by the
  comparisons for the composite `c = i ≫ j`.
- `map_eq_iff_pullHom_eq`: for `φ : a^* M ⟶ a'^* M'`, the equation
  `j^*(φ) = m(a, j, a₁)⁻¹ ≫ φ₁ ≫ m(a', j, a₁')` holds if and only if
  `pullHom φ j a₁ a₁' = φ₁`. This uses Mathlib's `map_eq_pullHom`.

## Squares

Fix a commuting square `w : i₁ ≫ j₁ = i₂ ≫ j₂` with `i₁ : X₀ ⟶ X₁`,
`i₂ : X₀ ⟶ X₂`, `j₁ : X₁ ⟶ X` and `j₂ : X₂ ⟶ X`.

- `squareIso F w Z : i₁^* (j₁^* Z) ≅ i₂^* (j₂^* Z)` (definition, for `Z` over
  `X`) is `m(j₁, i₁, i₁ ≫ j₁)⁻¹` followed by `m(j₂, i₂, i₁ ≫ j₁)`. It is the
  canonical identification of the two restrictions of `Z` to `X₀`.
  `squareIso_eq` says that the same formula holds with any morphism `c` in
  place of `i₁ ≫ j₁`, given `i₁ ≫ j₁ = c` and `i₂ ≫ j₂ = c`.
- `IsSquareEffective F w` (definition, a proposition) says that objects glue.
  For all `M₁` over `X₁`, `M₂` over `X₂` and every isomorphism
  `e : i₁^* M₁ ≅ i₂^* M₂`, there are `Z` over `X` and isomorphisms
  `e₁ : j₁^* Z ≅ M₁`, `e₂ : j₂^* Z ≅ M₂` such that
  `squareIso F w Z ≪≫ i₂^*(e₂) = i₁^*(e₁) ≪≫ e`.
- `IsSquareHomGluing F w` (definition, a proposition) says that morphisms glue
  uniquely. For all `Z`, `Z'` over `X` and morphisms
  `φ₁ : j₁^* Z ⟶ j₁^* Z'`, `φ₂ : j₂^* Z ⟶ j₂^* Z'` with
  `i₁^*(φ₁) ≫ squareIso Z' = squareIso Z ≫ i₂^*(φ₂)`, there is exactly one
  `φ : Z ⟶ Z'` with `j₁^*(φ) = φ₁` and `j₂^*(φ) = φ₂`.

These are the conditions that, for line bundles, say that the published
comparison functor to gluing data is essentially surjective, respectively full
and faithful. That translation is in the companion module
`Langlands.AlgebraicGeometry.Picard.FlatPicardSquareGluing`.

- `squareIso_comm_iff`: the compatibility condition in `IsSquareHomGluing` is
  equivalent to `pullHom φ₁ i₁ c c = pullHom φ₂ i₂ c c` for `c = i₁ ≫ j₁`.
- `IsSquareHomGluing.existsUnique_pullHom`: the same unique gluing for
  morphisms `a^* M ⟶ a'^* M'` between pullbacks of objects `M` over `V` and
  `M'` over `V'` along maps `a : X ⟶ V` and `a' : X ⟶ V'`. The data on the
  two middle corners are given through `pullHom` with prescribed names for all
  composites. Proof: apply `IsSquareHomGluing` to `a^* M` and `a'^* M'`,
  translating with `squareIso_comm_iff`, `pullHom_conj` and
  `map_eq_iff_pullHom_eq`.
- `pullIso_symm_trans_pullIso_of_effective`: rewrites the compatibility
  produced by `IsSquareEffective` with `pullIso` when `M₁ = f₁^* N₁` and
  `M₂ = f₂^* N₂` are themselves pullbacks. It then reads
  `m(f₁, i₁, d₁) ≪≫ e ≪≫ m(f₂, i₂, d₂)⁻¹ =
  (pullIso e₁ i₁ c d₁)⁻¹ ≪≫ pullIso e₂ i₂ c d₂`.

## Precomposition with a functor

For a functor `G : C ⥤ D` and a pseudofunctor `P` on `D`, consider
`G.op.toPseudofunctor.comp P`. The relative Picard pseudofunctor has this form.

- `comp_mapComp'`: its composition comparisons are those of `P` at the images
  under `G`.
- `squareIso_comp`: its `squareIso` on a square is the `squareIso` of `P` on
  the image square.

## Points

Here `Points F ξ η Z` is the published actual point fibre
(`Langlands.CategoryTheory.PseudofunctorPointFiber.Points`). For `ξ` over `U`,
`η` over `T` and `Z : Over T`, a point is a map `a : Z.left ⟶ U` together with
an isomorphism `a^* ξ ≅ (Z.hom)^* η`. `restrict` is its restriction along a
slice morphism.

- `pullHom_comp'`, `pullHom_id'` and `pullIso_symm`: `pullHom` preserves
  composition and identities, and `pullIso` preserves inverses.
- `restrict_eq`: the restriction of a point can be written with any prescribed
  name `a` for its new base map, given `q.left ≫ x.1 = a`.
  `mk_eq_mk_iff`: two points with the same base map are equal exactly when
  their isomorphisms are equal.
- `exists_glued_point` (G2): let `w : i₁ ≫ j₁ = i₂ ≫ j₂` be a square with total
  corner `T` on which `IsSquareHomGluing F w` holds. Let `c` satisfy
  `i₁ ≫ j₁ = c` and `i₂ ≫ j₂ = c`. Let `x₁` and `x₂` be points over
  `Over.mk j₁` and `Over.mk j₂` whose restrictions to `Over.mk c` agree. Let
  `g : T ⟶ U` satisfy `j₁ ≫ g = x₁.1` and `j₂ ≫ g = x₂.1`. Then there is a
  point `z` over `Over.mk (𝟙 T)` with `z.1 = g` whose restrictions along `j₁`
  and `j₂` are `x₁` and `x₂`. Proof: glue the two isomorphisms and their
  inverses with `existsUnique_pullHom`; the composites restrict to identities,
  so uniqueness makes the glued morphism an isomorphism.
- `exists_lift_of_square_gluing` is the lifting step. Its data are
  `p : K ⟶ U`, `i : B ⟶ A`, `rA : K ⟶ A`, `rB : K ⟶ B` with
  `rB ≫ i = rA`, `rD : K ⟶ D`, and `j₁ j₂ : A ⟶ P`, `jD : D ⟶ P`. These
  form two commuting squares, `w₁ : i ≫ j₁ = i ≫ j₂` and
  `w₂ : rA ≫ j₁ = rD ≫ jD`. Assume:
  - `IsSquareEffective F w₁`;
  - `IsSquareHomGluing F w₂`;
  - maps to `U` glue along the second square: for `g₁ : A ⟶ U` and
    `g₂ : D ⟶ U` with `rA ≫ g₁ = rD ≫ g₂`, there is `g : P ⟶ U` with
    `j₁ ≫ g = g₁` and `jD ≫ g = g₂`;
  - points lift along `rD` at `p`: for every `Z` over `P` and every point
    `y` over `Over.mk (rD ≫ jD)` with `y.1 = p`, there is a point over
    `Over.mk jD` restricting to `y`.

  Then every point `y` with values in `N` (over `A`) over `Over.mk i` with
  `rB ≫ y.1 = p` lifts to a point over `Over.mk (𝟙 A)` restricting to `y`,
  provided `y.1` extends along `i`, that is, `i ≫ u = y.1` for some
  `u : A ⟶ U`.

## Implemented proof of the lifting step

The proof follows the proof of Stacks Lemma 90.13.2. In the application, `A`,
`B`, `D` and `K` are the spectra of an Artinian ring `A`, of its quotient `B`,
of the dual numbers `D`, and of the residue field. `P` is the spectrum of
`A ×_B A ≅ A ×_K D`. With `u` as above:

1. Glue `u^* ξ` over the first copy of `A` and `N` over the second copy along
   the isomorphism over `B` given by `y`. This uses `IsSquareEffective F w₁`
   and gives `Z` over `P`, `e₁ : j₁^* Z ≅ u^* ξ` and `e₂ : j₂^* Z ≅ N`
   (applied to `(𝟙 A)^* N`).
2. `⟨u, e₁⁻¹⟩` is a point of `ξ` with values in `Z` over `Over.mk j₁`. Its
   restriction to `K` has base map `rA ≫ u = p`. Lifting along `rD` gives a
   point `wpt` over `Over.mk jD` with the same restriction.
3. The base maps `u` and `wpt.1` glue to `g : P ⟶ U`. `exists_glued_point`
   glues the two points to a point `z` over `P` with `z.1 = g`.
4. The lift is the restriction of `z` along the second copy `j₂`, transported
   through `e₂`. Its restriction along `i` equals `y`. The proof rewrites
   `y`'s isomorphism with `pullIso_symm_trans_pullIso_of_effective` and then
   computes with `pullIso_trans`, `pullIso_pullIso`, `pullIso_symm` and
   `pullIso_congr`, using `w₁`.

## Provenance

The definitions and results are internal. The lifting step is the part of the
proof of Stacks Project Lemma 90.13.2 (Tag 06IU, Chapter 90 Formal Deformation
Theory) that combines conditions (S1) and (S2) with ring-map lifting and
surjectivity on tangent spaces. Here it is stated for actual points of a
pseudofunctor, with its gluing inputs as explicit hypotheses. No source
statement is transcribed.
