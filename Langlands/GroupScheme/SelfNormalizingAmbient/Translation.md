# Smooth closed subgroups of corepresented groups in algebra terms

This module translates scheme-level hypotheses on a corepresented affine group scheme
`Spec B` over `Spec R` and on a closed subgroup of it into statements about the `R`-algebras
`B` and `B ⧸ I`. Smoothness of `Spec B` over `Spec R` becomes `Algebra.Smooth R B`. A smooth
closed subgroup with geometrically connected fibres is cut out by an ideal `I` of `B` such
that `B ⧸ I` is a smooth `R`-algebra and `k ⊗[R] (B ⧸ I)` is a domain for every field `k`
over `R`.

## Provenance

This module is internal supporting content for the task proving
`Langlands.GroupScheme.SelfNormalizingProperAmbientStatement`. Its algebraic statements are
standard consequences of the definitions: a morphism `Spec S → Spec R` is smooth exactly when
`R → S` is smooth, and a closed immersion into `Spec B` is `Spec (B ⧸ I)` for an ideal `I`.
The description of the points of the subgroup repeats the published proof of
`Langlands.GroupScheme.Corepresented.exists_ideal_range` (module
`Langlands.GroupScheme.NormalizerRepresentability`). That theorem hides the isomorphism
with `Spec (B ⧸ I)` inside its existential, and the smoothness transfer needs it. The domain
property of the fibres is the bridge
`Langlands.GroupScheme.SelfNormalizingAmbient.isDomain_tensor_of_smooth_geometricallyConnected`
(module `Langlands.GroupScheme.SelfNormalizingAmbient.FibreDomain`). No outside source is
ported here.

## Conventions

`R : CommRingCat.{u}`, `F : CommAlgCat R ⥤ GrpCat` is a group functor, and
`e : (F ⋙ forget GrpCat).CorepresentableBy B` corepresents it by the `R`-algebra
`B : CommAlgCat R`. `groupScheme F e` is the published group scheme `Spec B` over `Spec R`;
its structure morphism is `Spec.map (CommRingCat.ofHom (algebraMap R B))`. For a test scheme
`U` over `Spec R` and a point `y : U ⟶ (groupScheme F e).X`, `pointsEquiv F e U y` is the
corresponding group element and `e.homEquiv.symm` turns it into its classifying algebra map
from `B` to the global sections of `U`. `SubgroupFunctor.range j` is the subgroup functor of
points that factor through `j`. `Smooth`, `GeometricallyConnected` and `IsClosedImmersion`
are Mathlib's morphism properties; `Algebra.Smooth` and `IsDomain` are Mathlib's classes.

## Declarations

All declarations live in the namespace `Langlands.GroupScheme.Corepresented`. The module
imports `Langlands.GroupScheme.NormalizerRepresentability` and
`Langlands.GroupScheme.SelfNormalizingAmbient.FibreDomain`.

- `algebraSmooth_of_smooth_spec h`: for commutative rings `R S : Type u` with `[Algebra R S]`,
  if `h : Smooth (Spec.map (CommRingCat.ofHom (algebraMap R S)))`, then `Algebra.Smooth R S`.
- `smooth_of_smooth_groupScheme h`: if `h : Smooth (groupScheme F e).X.hom`, then
  `Algebra.Smooth R B`.
- `exists_ideal_range_smooth j hs hc`: let `K : GroupScheme (Spec R)` and
  `j : K ⟶ groupScheme F e` with `[IsClosedImmersion j.hom.hom.left]`, and assume
  `hs : Smooth K.X.hom` and `hc : GeometricallyConnected K.X.hom`. Then there is an ideal
  `I : Ideal B` with three properties:
  1. for every `U : Over (Spec R)` and every `y : U ⟶ (groupScheme F e).X`,
     `y ∈ (SubgroupFunctor.range j).carrier U` holds exactly when
     `(e.homEquiv.symm (pointsEquiv F e U y)).hom b = 0` for all `b ∈ I`;
  2. `Algebra.Smooth R (B ⧸ I)`;
  3. for every field `k : Type u` with `[Algebra R k]`, `IsDomain (k ⊗[R] (B ⧸ I))`.

  The first property is exactly the conclusion of the published `exists_ideal_range`, so it
  can be passed as the hypothesis `hI` of the published normalizer results.

## Proof

**Smooth spectra.** Mathlib's `HasRingHomProperty.Spec_iff` for `Smooth` turns
`Smooth (Spec.map φ)` into `RingHom.Smooth φ`, and `RingHom.smooth_algebraMap` identifies
`RingHom.Smooth (algebraMap R S)` with `Algebra.Smooth R S`. This proves
`algebraSmooth_of_smooth_spec`. The structure morphism of `groupScheme F e` is
`Spec.map (CommRingCat.ofHom (algebraMap R B))` by definition (`algSpec_obj_hom`), which gives
`smooth_of_smooth_groupScheme`.

**The ideal.** `IsClosedImmersion.Spec_iff` gives an ideal `I` of `B` and an isomorphism
`ε` from `K.X.left` to `Spec (B ⧸ I)` with `j.hom.hom.left = ε.hom ≫ Spec.map (mk I)`.
Since `j` is a morphism over `Spec R`, `K.X.hom = j.hom.hom.left ≫ (groupScheme F e).X.hom`
(`Over.w`). The composite `Spec.map (mk I) ≫ Spec.map (algebraMap R B)` is
`Spec.map (algebraMap R (B ⧸ I))` (`Spec.map_comp`). Together these give
`Spec.map (algebraMap R (B ⧸ I)) = ε.inv ≫ K.X.hom`.

**Smoothness and fibres.** Composing with the isomorphism `ε.inv` preserves smoothness (an
isomorphism is smooth and smooth morphisms compose). It also preserves geometric
connectedness, which respects isomorphisms because it is stable under base change
(`MorphismProperty.IsStableUnderBaseChange.respectsIso`). So
`Spec (B ⧸ I) → Spec R` is smooth and geometrically connected. `algebraSmooth_of_smooth_spec`
gives `Algebra.Smooth R (B ⧸ I)`, and `isDomain_tensor_of_smooth_geometricallyConnected`
gives the domain property of every field fibre.

**Points.** This part repeats the proof of `exists_ideal_range`. By
`homEquiv_symm_pointsEquiv_apply`, the classifying map of `y` evaluated at `b` is the
pullback of `b` along `y.left` to the global sections of `U`. The published criterion
`factorsThrough_affineQuotient_iff` says that `y.left` factors through
`Spec.map (mk I)` exactly when this map kills `I`. A point `t ≫ j` of the range factors
through `t.left ≫ ε.hom`. Conversely, if `y.left = z ≫ Spec.map (mk I)`, then `z ≫ ε.inv` is a
morphism over `Spec R` (by the formula for `K.X.hom`) whose composite with `j` is `y`.
