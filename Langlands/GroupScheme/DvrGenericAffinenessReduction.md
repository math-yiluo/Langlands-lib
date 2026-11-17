# Reduction of Raynaud affineness to two prerequisites

Worker 528.

This internal derived module reduces
`Langlands.GroupScheme.DvrGenericAffinenessStatement.{u}` to the two explicit
premises `SmoothDvrGenericAffinenessStatement.{u}` and
`DvrFiniteSmoothCoverStatement.{u}`. It does not prove either premise, and it
does not give an unconditional proof of Raynaud's criterion. Every declaration
works in the arbitrary universe `u` of the unchanged Library target.

`Langlands.GroupScheme.DvrGenericAffinenessReductionStatement.{u}` is the
Prop-valued definition of precisely this implication:

```text
SmoothDvrGenericAffinenessStatement.{u} →
  DvrFiniteSmoothCoverStatement.{u} → DvrGenericAffinenessStatement.{u}.
```

The remaining declarations belong to the namespace
`Langlands.GroupScheme.DvrGenericAffinenessReduction`. The theorem
`dvrGenericAffinenessReduction` proves the named conditional proposition by
applying `dvrGenericAffineness_of_smooth_and_cover`. This supporting statement
and its conditional proof do not supply the unconditional proof required by
the original task.

The imported `AffineQuotient.isAffine_of_finite_surjective` specializes the published algebraic-space theorem
`Langlands.AlgebraicGeometry.AlgebraicSpace.finiteSurjectiveAffineDescent` to actual
schemes. The scheme-to-space functor carries finite surjective scheme morphisms
to finite surjective space morphisms, by Mathlib's `MorphismProperty.relative_map`.
The affine source represents an affine algebraic space, so the descent theorem
supplies an affine scheme representing the target. Full faithfulness of scheme
Yoneda identifies that affine representing scheme with the original target.

`dvrGenericAffineness_of_smooth_and_cover` proves the original criterion
conditionally on the two named prerequisites. For its substantive direction,
the cover premise provides a flat surjective map `Spec R' → Spec R` with `R'` a
DVR and a finite surjective morphism from a smooth separated finite-type group
`H` to the actual base change of `G`. The cover also supplies affineness of the
actual generic fibre of `H` over the canonical `FractionRing R'`. The smooth
premise makes `H` affine. Finite-surjective descent makes the base change of
`G` affine, and the published
`FaithfullyFlatAffineDescent.isAffine_of_isPullback` descends its affineness over
the flat surjective affine base map. As `Spec R` is affine, affineness of the
total scheme yields relative affineness. The other direction uses Mathlib's
instance that affine morphisms are separated.

The provenance is the two-stage reduction in Prasad–Yu, *On quasi-reductive group
schemes*, author preprint, Proposition 3.1, PDF/printed p.5, registered source
`prasad-yu-2006-quasi-reductive-author-preprint`, SHA-256
`138d931a21fa522d97449c77acf429918826b1ef649be940d4721d616a1fc73b`.
The implementation uses the finite smooth cover as an explicit premise;
it does not construct a normalization, a DVR extension, or an affinization.
The two descent steps reuse published Library theorems and introduce no new
geometric assumptions. Finite-surjective descent for schemes is the
scheme specialization of the published Stacks Project Tag 07VS theorem.
