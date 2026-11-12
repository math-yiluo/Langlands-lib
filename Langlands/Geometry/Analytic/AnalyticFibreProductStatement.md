# Statement: the glued fibre product is a fibre product of analytic spaces

Author: Worker 21.

This module states, without proof, that the fibre product of saturated
presentations of `AnalyticFibreProduct` is a pullback in the localized
category of analytic spaces.

## The statement

`FibreProductPullbackStatement : Prop` (namespace
`Langlands.Analytic.SaturatedAtlasPresentation`). Let `K` be a complete,
ultrametric normed field in universe `u`. Let `X`, `Y`, `S` be saturated
presentations in `SaturatedAtlasPresentation.{u, u, u} K` whose spaces are
Hausdorff, and let `f : X ⟶ S`, `g : Y ⟶ S` be strong maps. Then the square

```text
localizationFunctor.map (fibreProductFst f g) : X ×_S Y → X
localizationFunctor.map (fibreProductSnd f g) : X ×_S Y → Y
localizationFunctor.map f : X → S,   localizationFunctor.map g : Y → S
```

is a pullback square in `LocalizedCategory` (Mathlib's `IsPullback`): for
every analytic space `T` and morphisms `φ : T → X`, `ψ : T → Y` with
`φ ≫ f = ψ ≫ g`, there is a unique morphism `T → X ×_S Y` whose composites
with the two projections are `φ` and `ψ`. The square commutes by
`localizationFunctor_fibreProduct_condition`; the statement adds the existence
and uniqueness of the factorization.

## Original source

Berkovich, *Étale cohomology for non-Archimedean analytic spaces* (1993),
registered as `berkovich-1993-etale-cohomology`, SHA256
`06b42aca1c8f237e607d2cf1f15a41fdc9718324a4dc9fd5bce66574254bb91c`:

- Proposition 1.4.1, printed p.29 / PDF p.26: "The category Φ_k-𝒜n admits
  fibre products."
- Printed p.30 / PDF p.27: "It is easy to see that the canonical projections
  Y' → Y and Y' → X' are morphisms of Φ_k-analytic spaces and that Y' is a
  fibre product of Y and X' over X in the category Φ_k-𝒜n."

The Library's `LocalizedCategory` is its construction of this category of
analytic spaces: strong maps of presentations localized at
quasi-isomorphisms (Berkovich 1993, after Proposition 1.2.10). The statement
transcribes the source for the fibre product constructed by gluing the
affinoid pushouts `V ×_W U` (`FibreProductChartSystem`, `FibreProductAtlas`).

Derived choices:

- The hypotheses are restricted to strong maps between saturated presentations
  with Hausdorff spaces, as in the construction. Berkovich's 1996 manuscript
  (`provided-7bb3903652336bd799aad8853b8efd7ff3bcc0c7652745417f4745a14ac08e90`,
  §1.1, printed p.1) assumes all analytic spaces Hausdorff. The test space `T`
  is arbitrary.
- The equal universes `u` for the field, the spaces and the chart indices are
  those of `AnalyticFibreProduct`.

## Expected proof route

None of this is formalized here.

1. By the Library's right calculus of fractions (`SaturatedLocalizedFractions`),
   write `φ` and `ψ` with a common quasi-isomorphic denominator. Refine further
   until the two numerators `a`, `b` satisfy `a ≫ f = b ≫ g` as strong maps.
2. Build the factorization as an admissible pair system into the glued fibre
   product: on the charts of `T` mapping into a pair chart `V ×_W U`, the
   pushout lift of the two pullbacks. Turn it into a morphism of the localized
   category with the Library's `pairSystemLocalizedHom`.
3. Uniqueness: a map into a pair chart is determined by its two composites with
   the legs (`AffinoidPushout.hom_ext`).

## Scope

This is a `lean.statement`: nothing is proved here.
