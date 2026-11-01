# Finite support from rational-fibre vanishing on the second square projection

`Langlands.AbelianScheme.SquareSecondProjectionSupportStatement` is a
proposition target for the finite-support step in second-projection
cohomology detection. This module states the proposition; it does not prove it.

Let `K : Type u` be a field with `IsAlgClosed K`, and let `A` be an actual
abelian scheme over `Spec K`. Write `a := A.X.hom`,
`Z := pullback a a`, and `p2 := pullback.snd a a`. Let `Q` be a line
bundle on `Z`, and let `F` be a finite set of actual rational points,
represented by morphisms `Over.mk (𝟙 (Spec K)) ⟶ A.X`.
The hypothesis says that for every such point `x` outside `F` and every
`n : ℕ`, the actual `K`-module

```text
(DerivedSections.relativeCohomology a n).obj
  ((LineBundle.pullback (squareSecondInclusion a x.left x.w)).obj Q).obj
```

is zero. Here `squareSecondInclusion` is the published pullback lift
with components `𝟙 A.X.left` and `a ≫ x.left`; the section equation
`x.w` identifies its image with the second-projection fibre `A × {x}`.

The conclusion says that for every `n : ℕ`, the actual scheme module
`(DerivedSections.higherDirectImage p2 n).obj Q.obj` has
`HasFiniteClosedSupport`. By the imported `ModuleSupport` definition,
its locus of nonzero underlying abelian-group stalks is finite, and
every point in that locus is closed. The conclusion does not identify
that locus with `F`, or require every point of `F` to occur in it.

Both degree quantifiers include zero. The common universe `u` is
arbitrary. There is no characteristic, positive-dimension, nonempty-`F`,
coherence or total-cohomology hypothesis. Smoothness and properness are
properties of the actual abelian scheme; no additional geometric
certificate is an outer premise.

## Provenance and role

This is an internal derived statement, using the published actual
line-bundle, scheme-cohomology, second-fibre and module-support
interfaces. It isolates the finite-support conclusion needed by
`AlgClosedFieldSquareSecondProjectionFiniteSupportDetectionStatement`.
It transcribes no additional assertion from external literature.

The intended deduction takes the open complement of the underlying
points of `F`, transfers the fibre hypothesis by
`squareSecondFibreCohomologyIso`, applies the published open-local
rational-fibre vanishing theorem with the published
`universalPerfectSections` proof, and then uses
`hasFiniteClosedSupport_of_isZero_rationalPointComplement`.
This paragraph describes the derivation motivating the target, not a
proof supplied by this statement module.

Finite-support cohomology and zero detection, the finite-support Leray
comparison, reverse affine base change, and the final total-cohomology
argument remain separate from this proposition.
