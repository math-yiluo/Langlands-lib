# Proof: the affine agreement locus from the noetherian case and noetherian approximation

Author: Worker 848.

This module proves the published proposition
`Langlands.AbelianScheme.RigidifiedClassesEqualizerClosedAffineFromNoetherianStatement`:

```lean
theorem Langlands.AbelianScheme.rigidifiedClassesEqualizerClosedAffine_of_noetherian :
    RigidifiedClassesEqualizerClosedAffineFromNoetherianStatement.{u}
```

That proposition is the implication
`RigidifiedClassesEqualizerClosedNoetherianAffineStatement.{u} →
RigidifiedClassesNoetherianApproximationStatement.{u} →
RigidifiedClassesEqualizerClosedAffineStatement.{u}`. The theorem proves this implication only: it
proves neither the noetherian case nor the approximation statement, so it does not by itself prove
the affine statement `RigidifiedClassesEqualizerClosedAffineStatement`.

## Provenance

This is the formal last step of the standard reduction to the noetherian case by limit arguments
(Stacks Project, Chapter 32 "Limits of Schemes", registered `stacks-limits-of-schemes-a04446e5`):
a closed subscheme of the noetherian base, pulled back to `Spec R`, represents the same condition.
The statements combined here are derived from Stacks tags 0BDP and 0BF0 (registered
`stacks-picard-diagonal-seesaw-0bdp-0bf0-a04446e5`); see their own Markdown files. The Lean proof is
original to this project.

## Proof

Introduce the two hypotheses `hNoeth` (noetherian case) and `hApprox` (approximation), then fix
`R`, an abelian scheme `A` over `Spec R` and rigidified classes `q`, `r` over
`Over.mk (𝟙 (Spec R))`.

1. The approximation hypothesis gives a noetherian ring `R₀` in universe `u`, a ring map
   `φ : R₀ ⟶ R`, an abelian scheme `A₀` over `Spec R₀` and classes `q₀`, `r₀` such that, for every
   `h : T' ⟶ Over.mk (𝟙 (Spec R))`, the pullbacks of `q` and `r` along `h` are equal exactly when
   the pullbacks of `q₀` and `r₀` along
   `Over.homMk (T'.hom ≫ Spec.map φ) : Over.mk (T'.hom ≫ Spec.map φ) ⟶ Over.mk (𝟙 (Spec R₀))` are
   equal.
2. The noetherian hypothesis, applied to `R₀`, `A₀`, `q₀`, `r₀` (with the instance supplied by the
   existential witness), gives a closed immersion `ι₀ : Z₀ ⟶ Spec R₀` such that a morphism into
   `Over.mk (𝟙 (Spec R₀))` factors through `ι₀` exactly when the pullbacks of `q₀` and `r₀` along it
   agree.
3. Take `Z := pullback ι₀ (Spec.map φ)` and `ι := pullback.snd ι₀ (Spec.map φ)`. It is a closed
   immersion because closed immersions are stable under base change (Mathlib instance, found by
   `inferInstance`).
4. For `h : T' ⟶ Over.mk (𝟙 (Spec R))`, `h.left = T'.hom` by `Over.w h`. Chaining step 2 at
   `Over.mk (T'.hom ≫ Spec.map φ)` and step 1 reduces the goal to: `T'.hom` factors through `ι`
   exactly when `T'.hom ≫ Spec.map φ` factors through `ι₀`. Forward, compose a factorisation `g`
   with `pullback.fst` and use `pullback.condition`. Backward, a factorisation `g` with
   `g ≫ ι₀ = T'.hom ≫ Spec.map φ` gives `pullback.lift g T'.hom`, whose composite with
   `pullback.snd` is `T'.hom`.

## Use

Together with proofs of the two hypotheses (proof tasks `00ab6acd-8b6c-4595-8df8-3fbdac0bdd4d`
and `a825ba6f-ac5b-43b7-8794-52b2039388f7`), this gives the affine statement, which the reduction in task `e3d4a3ab-f378-42af-87c5-0cd4caec7b2e` uses to prove
the published `Langlands.AbelianScheme.RigidifiedClassesEqualizerClosedStatement`.
