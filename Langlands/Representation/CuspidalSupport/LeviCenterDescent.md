# Center descent for actual rational Levi functors

Worker 86. This is an internal supporting construction for Renard VI.10.5,
not a proof of `HarishChandraHomomorphismStatement`. The representation theoretic
existence of pointwise central lifts and module finiteness remain obligations.

The ambient data are a nonarchimedean local field with its Hausdorff topology,
an affine group scheme `G`, the canonical topology on `G(k)`, local compactness
and the nonarchimedean group property, and an actual rational parabolic `P = MU`
with its rational Levi, geometric unipotent radical and multiplication
isomorphism. Group and carrier universes are independent. For the adjunction
and center maps, carriers are in the common universe `max u v`, exactly as in
the Harish-Chandra statement. No irreducibility, supercuspidality,
admissibility or finite length is needed for these constructions.

`leviFirstAdjunction` packages the published first adjunction for the literal
Levi image and transports it along the published smooth pullback equivalence.
The published radical theorem supplies its unimodularity premise. Composing
the two adjunctions gives `R ⊣ I` for the actual `leviJacquetFunctor` and
`leviInductionFunctor`. Thus this adjunction requires no additional structural
premise. It is the same-parabolic first adjunction; the opposite-parabolic
second adjunction remains separate.

`leviInductionFunctor_additive` checks addition of induced morphisms by
evaluating the actual functions. The published unconditional faithfulness
theorem and this additivity proof then specialize `faithfulCenterDescent`.
Its premise `CenterComponentsLift I` asks, for every target central
transformation `z` and every smooth Levi representation `σ`, for an
endomorphism of `σ` whose induced map equals `z.app (I.obj σ)`. Under that
explicit premise, `leviCenterDescent` is a unital ring homomorphism from the
actual smooth `G(k)` category center to the actual smooth `M(k)` category
center. The induction equation is the defining equation of its chosen lifts.
The Jacquet equation follows from `faithfulCenterDescent_leftAdjoint` and the
actual first adjunction. Uniqueness follows from faithfulness on components.

The construction is derived directly from the imported categorical and
representation theoretic results. It verifies their applicability to the
exact functors and universes used by VI.10.5. It supplies neither
`CenterComponentsLift I` unconditionally nor a finite-module conclusion, and
therefore does not discharge any of the four complete host-task targets.
