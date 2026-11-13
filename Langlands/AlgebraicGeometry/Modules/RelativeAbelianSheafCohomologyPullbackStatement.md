# Relative module cohomology and arbitrary sheaf-cohomology pullback

Author: Worker 221.

`Langlands.AlgebraicGeometry.Modules.AbelianSheafComparison.RelativeAbelianSheafCohomologyPullbackStatement.{u}` is an internal, `Prop`-valued statement target. It adds no axiom and does not provide a proof.

## Data and assertion

Let `R : CommRingCat.{u}`, let `X, X'` be schemes over `Spec R`, and let `f : X' ⟶ X` be a morphism over that base. Let `M` be an actual `X.left`-module, `N` an actual `X'.left`-module, and `k : M ⟶ f_* N` a module morphism. There are no compactness, immersion, nilpotence, or flatness assumptions. The statement quantifies over every natural degree `n` and every element of `Sheaf.H ((toAbSheaf X.left).obj M) n`.

The coefficient arrow `k` gives an arrow of underlying abelian sheaves

```text
(toAbSheaf X.left).obj M → f.base_* ((toAbSheaf X'.left).obj N).
```

Here forgetting the module structure commutes definitionally with direct image. `AbelianSheafCohomologyPullback.pushforwardMap f.left.base ((toAbSheaf X.left).map k) n` is the map on actual Ext-defined sheaf cohomology: it uses exact inverse image of abelian sheaves, the canonical constant-sheaf comparison, and the adjoint of this arrow under the sheaf inverse-image/direct-image adjunction.

Write `ρ_M = relativeHAddEquiv X.hom M n` and `ρ_N = relativeHAddEquiv X'.hom N n`. These are the existing additive comparisons with actual relative module cohomology, obtained by forgetting the module structure and restricting scalars along the specified structure morphisms. The assertion is

```text
ρ_N (pushforwardMap(f, k)(x)) = Hⁿ(c) (relativeCohomologyPullback(f, M)(ρ_M(x))),
```

where `c : f^* M ⟶ N` is the adjoint of `k` under `Scheme.Modules.pullbackPushforwardAdjunction f.left`, and `Hⁿ(c)` is the map of `DerivedSections.relativeCohomology X'.hom n`. The module pullback on the right is the unchanged injective-resolution and bounded-below-derived-sections construction from `Modules.CohomologyPullback`.

## Provenance and intended use

This is an internal comparison obligation between two existing constructions, formulated for Task 5898. It is not a transcription of a separate literature theorem. Its meaning is determined by the imported definitions of actual module cohomology, actual underlying abelian sheaves, their additive comparison, and the Ext-defined inverse-image map. The sheaf and module pullback adjunctions are fixed independently; the assertion requires compatibility of the resulting maps, rather than accepting an arbitrary comparison or cohomology map as an input.

Applied in degree two to the ideal modules of a square-zero thickening, it supplies the module-cohomology comparison needed by `SquareZeroObstructionMorphismNaturalityStatement`. Naturality of the unit sequence and the Picard/unit-H¹ comparison remain separate obligations. This statement does not assert the Picard obstruction result or any downstream lifting theorem.
