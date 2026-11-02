# Inner automorphisms form a group homomorphism

Author: Worker 1220.

This module extends the published `Langlands.GroupScheme.InnerAutomorphism`. It works
over an arbitrary base scheme `S` and for an arbitrary group scheme `G` over `S`, with
no affineness or commutativity assumptions. It proves that the published inner
automorphism `innerIso G g : G ≅ G` of a base point `g : Over.mk (𝟙 S) ⟶ G.X` depends
multiplicatively on `g`, packages this as a group homomorphism into `Aut G`, and records
how restrictions of inner automorphisms along a homomorphism `i : H ⟶ G` compose.

It is a helper for task 6edfb074. There the last three lemmas are meant to show that the
centralizer points of a maximal split torus form a normal subgroup of its normalizer
points, so that the relative Weyl group `N(k)/Z(k)` is a quotient group. That
relative-roots module is not yet written. All declarations are in the namespace
`Langlands.GroupScheme`.

## Provenance (internal)

These are internal facts about the Library's own `constantPoint` and `innerIso`
constructions. They are the scheme-level form of the identities
`Int(gh) = Int(g) ∘ Int(h)`, `Int(1) = id` and `Int(g⁻¹) = Int(g)⁻¹` for conjugation
`Int(g)(x) = g x g⁻¹` in a group. Every proof checks the identity on points of every
test scheme `T`, using the published formula `comp_innerIso_hom`
(`x ≫ Int(g) = g_T * x * g_T⁻¹`) and the published extensionality lemma
`hom_ext_points` (two group-scheme homomorphisms agreeing on all points are equal).

## Lemmas on constant points

Here `g_T = constantPoint G g T` is the pullback of `g` to the test scheme `T`.

- `constantPoint_mul`: `(g * h)_T = g_T * h_T`.
- `constantPoint_inv`: `(g⁻¹)_T = (g_T)⁻¹`.
- `constantPoint_one`: `1_T = 1`.

All three hold because precomposition with a fixed morphism preserves the group
structure on points (Mathlib's `MonObj.comp_mul`, `GrpObj.comp_inv`, `MonObj.comp_one`).
They are the pointwise forms of the published homomorphism `constantPointHom` in
`Langlands.GroupScheme.HomConjugacy`, stated without that wrapper.

## Multiplicativity of inner automorphisms

- `innerIso_mul_hom`: `(innerIso G (g * h)).hom = (innerIso G h).hom ≫ (innerIso G g).hom`,
  that is, `Int(gh) = Int(g) ∘ Int(h)` in diagrammatic order. On a point `x` of `T` both
  sides are `(g_T * h_T) * x * (g_T * h_T)⁻¹`, after expanding the inverse of a
  product and reassociating.
- `innerIso_one_hom`: `(innerIso G 1).hom = 𝟙 G`. On points, `1 * x * 1⁻¹ = x`.
- `innerIso_inv_hom`: `(innerIso G g⁻¹).hom = (innerIso G g).inv`. It is obtained by
  cancelling the isomorphism `(innerIso G g).hom` on the left and applying the two
  previous lemmas to `g⁻¹ * g = 1`.
- `innerAut G : (Over.mk (𝟙 S) ⟶ G.X) →* Aut G`, the definition `g ↦ innerIso G g`.
  Mathlib's `Aut G` has multiplication `f * f' = f'.trans f`, composition in the order of
  functions, so `innerIso_mul_hom` is exactly the multiplicativity of this map and
  `innerIso_one_hom` gives `innerAut G 1 = 1`. The `@[simps]` attribute generates
  `innerAut_apply`.

## Restricting inner automorphisms along a homomorphism

For a homomorphism `i : H ⟶ G` and an automorphism `σ : H ≅ H`, the equation
`i ≫ (innerIso G n).hom = σ.hom ≫ i` says that conjugation by `n` maps the image of `i`
to itself and acts there through `σ`.

- `comp_innerIso_inv_hom`: if `i ≫ Int(n) = σ.hom ≫ i`, then
  `i ≫ Int(n⁻¹) = σ.inv ≫ i`. The proof rewrites `Int(n⁻¹)` as the inverse of `Int(n)`
  by `innerIso_inv_hom`, moves `σ` to the other side, and substitutes the hypothesis.
- `comp_innerIso_mul_hom`: if `i ≫ Int(n) = σ.hom ≫ i` and `i ≫ Int(m) = τ.hom ≫ i`,
  then `i ≫ Int(n * m) = (τ ≪≫ σ).hom ≫ i`. The proof expands `Int(n * m)` by
  `innerIso_mul_hom` and substitutes both hypotheses.
- `comp_innerIso_conj_hom`: if `i ≫ Int(n) = σ.hom ≫ i` and `i ≫ Int(z) = i`, then
  `i ≫ Int(n * z * n⁻¹) = i`. The proof expands `Int(n * z * n⁻¹)` into
  `Int(n⁻¹)`, `Int(z)` and `Int(n)` and substitutes the two hypotheses and
  `comp_innerIso_inv_hom`, leaving `σ.inv ≫ σ.hom ≫ i = i`.

The first two lemmas show that the base points `n` admitting such a `σ` are closed under
inverses and products. The third shows that those with `σ` the identity are stable under
conjugation by them.
