# Coinvariants of tensor products and the Hecke tensor product (Renard III.1.15): statements

Author: Worker 1222. Module `Langlands.Representation.Smooth.RenardCoinvariantTensorStatements`,
namespace `Langlands.Renard.Smooth`. Entry proposition `RenardCoinvariantTensorStatements`
(universe parameters `u', v'`), the conjunction of five closed `Prop`-valued statements. The
module also contains one Prop-valued helper predicate, `IsCheckRightAction`. It proves nothing.

## Original source

David Renard, *Représentations des groupes réductifs p-adiques*, French edition dated
**9 July 2026**, registered as `renard-2026-representations-groupes-reductifs-padiques`,
SHA256 `7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`. Worker 1222 read
III.1.14–III.1.15, printed pp.66–70 / PDF pp.72–76, II.3.7 (printed p.47 / PDF p.53) and the
Proposition of II.3.12 (printed p.52 / PDF p.58) for this unit.

Section III.1.15, printed p.69 / PDF p.75, reads after the Remarks:

> Soient `(π_i, V_i)`, `i = 1, 2` des représentations lisses de `G`. Intéressons nous
> maintenant à l'espace des coinvariants de `V_1 ⊗ V_2` pour l'action de `G` : par
> définition, il s'agit du quotient de `V_1 ⊗ V_2` par le sous-espace engendré par les vecteurs
> de la forme `π_1(g) · v_1 ⊗ π_2(g) · v_2 − v_1 ⊗ v_2`, `v_1 ∈ V_1`, `v_2 ∈ V_2`, `g ∈ G`.
> Notons-le `(V_1 ⊗ V_2)_G`. Grâce à l'équivalence de catégorie III.1.4, il est immédiat que
> `(V_1 ⊗ V_2)_G` s'identifie à `V_1 ⊗_{H(G)} V_2`, où la structure de `H(G)`-module à gauche
> sur `V_1` donnée par `π_1` est transformée en une structure de module à droite par
> l'anti-involution `T ↦ Ť` de `H(G)`. Soient `(π_i, V_i)`, `i = 1, 2, 3` des représentations
> lisses de `G`. De l'isomorphisme naturel (c'est un cas particulier de I.2.2.4)
> `(V_1 ⊗ V_2) ⊗ V_3 ≃ V_1 ⊗ (V_2 ⊗ V_3)`, on déduit, en prenant de chaque côté les
> coinvariants pour l'action de `G`,
>
> (III.1.15.1) `(V_1 ⊗ V_2) ⊗_{H(G)} V_3 ≃ V_1 ⊗_{H(G)} (V_2 ⊗ V_3)`.

Remark 3 of III.1.15, printed p.68 / PDF p.74, reads:

> Si `(ω, ℂ_ω)` est une représentation de dimension 1 de `G`, alors `• ⊗ ℂ_ω` réalise une
> équivalence de catégories d'inverse `• ⊗ ℂ_{ω^{-1}}`. De plus ces deux foncteurs sont
> adjoints, dans les deux sens possibles, c'est-à-dire que quelles que soient les
> représentations lisses `(π, V)` et `(ρ, W)` de `G`, on a un isomorphisme naturel
> `Hom_G(V, W ⊗ ℂ_ω) ≃ Hom_G(V ⊗ ℂ_{ω^{-1}}, W)`, l'autre adjonction étant obtenue en
> échangeant les rôles de `ω` et `ω^{-1}`. Ceci montre dans ce cas que le foncteur `• ⊗ ℂ_ω`
> est un adjoint à droite et à gauche et donc qu'il préserve les limites et les colimites. En
> particulier il est exact.

The section opens (printed p.67 / PDF p.73) with the functor `• ⊗ V : M(G) → M(G)`,
`(ρ, W) ↦ (ρ ⊗ π, W ⊗ V)`, for the tensor product representation of III.1.14 (printed p.66 /
PDF p.72); that this functor lands in `M(G)` is the smoothness of tensor products of smooth
representations, which the source uses without a separate statement.

The anti-involution is defined on distributions: II.3.12, Proposition, says that `H(G)` "est
munie de l'anti-involution `T ↦ Ť` induite par `g ↦ g^{-1}`", and the Proposition of II.3.7
gives `μ̌_G = δ_G^{-1} μ_G` for the modular function `δ_G`.

## Published objects used

- `SmoothRep`, `IsSmooth` and the twist functor `SmoothRep.twistFunctor ω hω` for a character
  `ω : G →* ℂˣ` with open kernel `hω`, which acts on the same carrier by `g ↦ ω(g) ρ(g)`
  (`Langlands.Representation.Category.Twist`).
- `HeckeAlgebra μ`, the Haar Hecke algebra of test functions with convolution for the left
  Haar measure `μ`, `HeckeAlgebra.toTestFunction`, `TestFunction.inversion` (`f ↦ (g ↦ f(g⁻¹))`,
  without a modular factor), `integratedAction ν ρ hρ f v = ∫ f(g) ρ(g) v dν(g)` for any measure
  `ν` finite on compacts, and `heckeNonUnitalModule μ ρ hρ`, the published left module structure
  of the Hecke algebra on a smooth representation through `heckeAction`
  (`Langlands.Representation.Hecke.NondegenerateModuleFunctor`).
- `NonUnitalModule`, and `NonUnitalModuleTensor.Tensor A X Y` with its pure tensors
  `NonUnitalModuleTensor.tmul`: for a right module `X` (a `NonUnitalModule Aᵐᵒᵖ X`) and a left
  module `Y` over a nonunital ring `A`, the quotient of `X ⊗_ℤ Y` by the balancing relations
  `(x · a) ⊗ y − x ⊗ (a · y)`. It is the `X ⊗_A Y` of I.2.1–I.2.2.
- From Mathlib: `Representation.tprod`, `Representation.Coinvariants` with
  `Representation.Coinvariants.mk` (the quotient of `V` by the span of the `ρ(g) x − x`),
  `Measure.inv` (the image of a measure under `g ↦ g⁻¹`), natural isomorphisms `F ⋙ G ≅ 𝟭`
  and adjunctions `F ⊣ G`.

The group hypotheses are those of the published III.1.4 statement
`HeckeNondegenerateModuleEquivalenceStatement`: `[TopologicalSpace G] [T2Space G]
[NonarchimedeanGroup G] [LocallyCompactSpace G]`, with `[MeasurableSpace G] [BorelSpace G]`
and a left Haar measure `μ` where the Hecke algebra occurs. Together they say that `G` is a
t.d. group in Renard's sense (II.1.1, a Hausdorff group with a basis of compact open subgroups
at the identity).

## Helper predicate

`IsCheckRightAction μ π hπ M`, for a smooth `π` on `V` and a structure
`M : NonUnitalModule (HeckeAlgebra μ)ᵐᵒᵖ V`, says that

```lean
∀ f x, (letI := M; op f • x) =
  integratedAction μ.inv π hπ (TestFunction.inversion (HeckeAlgebra.toTestFunction μ f)) x
```

The right side is `∫ f(g⁻¹) π(g) x dμ̌(g) = ∫ f(g) π(g⁻¹) x dμ(g)`. This is Renard's `π(Ť) x`
for the distribution `T = f μ`: `Ť` is the image of `f μ` under `g ↦ g⁻¹`, so
`π(Ť) x = ∫ π(g⁻¹) x f(g) dμ(g)`. In function terms `Ť = f̌ μ̌ = (f̌ δ_G^{-1}) μ` by II.3.7; the
predicate uses the inverted measure `μ.inv` and does not need the modular function. Since the
action of `M` is its only data, at most one structure satisfies the predicate.

## Statements

### `TensorProductSmoothStatement` (III.1.14–III.1.15)

For smooth `π₁`, `π₂` on `V₁`, `V₂` (both in `Type v`), `Representation.tprod π₁ π₂` is
smooth. This is the implicit claim that `• ⊗ V` is an endofunctor of `M(G)`; it also makes the
smoothness hypotheses of `HeckeTensorAssociativityStatement` satisfiable.

### `CheckRightActionExistsStatement` (III.1.15, the right module structure)

For every smooth `π` on `V` there is `M : NonUnitalModule (HeckeAlgebra μ)ᵐᵒᵖ V` with
`IsCheckRightAction μ π hπ M`: the operators `π(Ť)` form a right action of `H(G)`. This is the
source's "transformée en une structure de module à droite par l'anti-involution `T ↦ Ť`". It
makes the hypotheses `IsCheckRightAction` of the next two statements satisfiable.

### `CoinvariantHeckeTensorStatement` (III.1.15, the coinvariants)

For smooth `π₁`, `π₂` and every `M₁` with `IsCheckRightAction μ π₁ hπ₁ M₁`, with `V₂` a left
module through `heckeNonUnitalModule μ π₂ hπ₂`, there is an additive equivalence

```lean
e : Representation.Coinvariants (Representation.tprod π₁ π₂) ≃+
  NonUnitalModuleTensor.Tensor (HeckeAlgebra μ) V₁ V₂
```

with `e (Coinvariants.mk _ (x₁ ⊗ₜ x₂)) = tmul x₁ x₂` for all `x₁`, `x₂`. Mathlib's
`Coinvariants.ker` is the `ℂ`-span of the `ρ(g) x − x`, so `Coinvariants (tprod π₁ π₂)` is
exactly Renard's `(V₁ ⊗ V₂)_G`.

### `HeckeTensorAssociativityStatement` (III.1.15.1)

For representations `π₁`, `π₂`, `π₃` with `π₁` and `π₃` smooth, hypotheses `h₁₂`, `h₂₃` that `tprod π₁ π₂` and `tprod π₂ π₃` are
smooth, and right structures `M₁₂` on `V₁ ⊗[ℂ] V₂` and `M₁` on `V₁` satisfying
`IsCheckRightAction` for `tprod π₁ π₂` and `π₁`, there is an additive equivalence from
`Tensor (HeckeAlgebra μ) (V₁ ⊗[ℂ] V₂) V₃` (left structure on `V₃` from `π₃`) to
`Tensor (HeckeAlgebra μ) V₁ (V₂ ⊗[ℂ] V₃)` (left structure on `V₂ ⊗ V₃` from `tprod π₂ π₃`)
sending `(x₁ ⊗ₜ x₂) ⊗ x₃` to `x₁ ⊗ (x₂ ⊗ₜ x₃)`. The smoothness of `π₂` is not a separate
hypothesis; `TensorProductSmoothStatement` supplies `h₁₂` and `h₂₃` when all three are smooth.

### `TwistEquivalenceStatement` (III.1.15, Remark 3)

A one-dimensional smooth representation `(ω, ℂ_ω)` is a character `ω : G →* ℂˣ` with open
kernel, and `• ⊗ ℂ_ω` is `SmoothRep.twistFunctor ω hω`. For such `ω`, with `hω'` the openness
of the kernel of `ω⁻¹` (the same subgroup), the statement asserts:

1. `twistFunctor ω hω ⋙ twistFunctor ω⁻¹ hω' ≅ 𝟭` and
2. `twistFunctor ω⁻¹ hω' ⋙ twistFunctor ω hω ≅ 𝟭`, so that `• ⊗ ℂ_ω` is an equivalence with
   inverse `• ⊗ ℂ_{ω^{-1}}`;
3. `twistFunctor ω⁻¹ hω' ⊣ twistFunctor ω hω`, the natural isomorphism
   `Hom_G(V ⊗ ℂ_{ω^{-1}}, W) ≃ Hom_G(V, W ⊗ ℂ_ω)`;
4. `twistFunctor ω hω ⊣ twistFunctor ω⁻¹ hω'`, the adjunction with `ω` and `ω^{-1}`
   exchanged.

The Remark's last conclusions (preservation of limits and colimits, exactness) follow from 3
and 4 by Mathlib's `CategoryTheory.Adjunction.leftAdjoint_preservesColimits` and
`CategoryTheory.Adjunction.rightAdjoint_preservesLimits`; they are not restated.

## Provenance and departures from the source

The provenance is the source passages quoted above.

- **Ť.** See the helper predicate. The right structure is characterized by its action rather
  than constructed: constructing it needs the anti-multiplicativity of `f ↦ π(Ť_f)`, which is
  the content of `CheckRightActionExistsStatement`.
- **Additive equivalences.** `NonUnitalModuleTensor.Tensor` is an additive group; the source's
  `V₁ ⊗_{H(G)} V₂` is a complex vector space by I.2.1. The statements assert additive
  equivalences with the stated values on pure tensors. Since `Coinvariants.mk` is surjective and
  pure tensors generate, these formulas determine the maps. Naturality is not asserted; the
  source does not state it for these identifications.
- **"Grâce à l'équivalence de catégorie III.1.4".** The source's reason is not part of the
  statement.
- **Sizes.** All carriers lie in one universe `v`, independent of the universe `u` of `G`, as in
  the published `TensorHomAdjunctionStatement`.

## Relation to the Library

The Proposition, Lemma, Corollary and Theorem of III.1.15 are the published
`TensorHomAdjunctionStatement` and `TensorHomExactnessStatement`
(`Langlands.Representation.Smooth.RenardTensorHomStatements`). This module states the
remaining assertions of the section: the coinvariant identification, (III.1.15.1) and
Remark 3. Remarks 1 and 2 restate consequences of the published Corollary and are not stated
separately.

## Scope

This module states the listed assertions and proves none of them. Proofs belong to a separate
proof task.

## Imports

| Module | Used for |
| --- | --- |
| `Langlands.Representation.Hecke.NondegenerateModuleFunctor` | `HeckeAlgebra`, `heckeNonUnitalModule`, and through it `integratedAction`, `TestFunction.inversion`, `IsSmooth` |
| `Langlands.Algebra.NonUnitalModuleTensor` | `NonUnitalModuleTensor.Tensor`, `NonUnitalModuleTensor.tmul`, `NonUnitalModule` |
| `Langlands.Representation.Category.Twist` | `SmoothRep.twistFunctor` |
| `Mathlib.RepresentationTheory.Coinvariants` | `Representation.Coinvariants`, `Representation.Coinvariants.mk` |
