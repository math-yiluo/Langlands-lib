# The affine agreement locus from the noetherian case and noetherian approximation (statement)

Author: Worker 848.

This module defines one proposition and proves nothing:

```lean
def Langlands.AbelianScheme.RigidifiedClassesEqualizerClosedAffineFromNoetherianStatement : Prop :=
  RigidifiedClassesEqualizerClosedNoetherianAffineStatement.{u} →
    RigidifiedClassesNoetherianApproximationStatement.{u} →
      RigidifiedClassesEqualizerClosedAffineStatement.{u}
```

It is the implication "noetherian case and noetherian approximation together give the affine
case" between three published propositions, all in the namespace `Langlands.AbelianScheme`:

- `RigidifiedClassesEqualizerClosedAffineStatement` (module
  `Langlands.AlgebraicGeometry.Picard.RigidifiedClassesEqualizerClosedAffineStatement`): for every
  commutative ring `R` in universe `u`, every abelian scheme `A` over `Spec R` and every two
  rigidified classes `q`, `r` over `Over.mk (𝟙 (Spec R))`, there is a closed immersion
  `ι : Z ⟶ Spec R` such that, for every morphism `h : T' ⟶ Over.mk (𝟙 (Spec R))`, `h.left`
  factors through `ι` exactly when the pullbacks of `q` and `r` along `h` are equal.
- `RigidifiedClassesEqualizerClosedNoetherianAffineStatement` (module
  `Langlands.AlgebraicGeometry.Picard.RigidifiedClassesEqualizerClosedNoetherianStatement`): the
  same proposition restricted to noetherian rings `R`.
- `RigidifiedClassesNoetherianApproximationStatement` (module
  `Langlands.AlgebraicGeometry.Picard.RigidifiedClassesNoetherianApproximationStatement`): for
  every datum `(R, A, q, r)` as above there are a noetherian ring `R₀` in universe `u`, a ring map
  `φ : R₀ ⟶ R`, an abelian scheme `A₀` over `Spec R₀` and two rigidified classes `q₀`, `r₀` over
  `Over.mk (𝟙 (Spec R₀))` such that, for every `h : T' ⟶ Over.mk (𝟙 (Spec R))`, the pullbacks of
  `q` and `r` along `h` are equal exactly when the pullbacks of `q₀` and `r₀` along
  `Over.homMk (T'.hom ≫ Spec.map φ) : Over.mk (T'.hom ≫ Spec.map φ) ⟶ Over.mk (𝟙 (Spec R₀))` are
  equal. It asserts only this equivalence of agreement conditions, not that `A`, `q`, `r` are
  base changes of `A₀`, `q₀`, `r₀`.

The universe parameter `u` is shared by all three propositions. The definition asserts none of
them; it states only the implication.

## Provenance

Internal to this project. The implication is the last, formal step of the standard reduction of a
finite-presentation statement to the noetherian case by limit arguments (Stacks Project, Chapter 32
"Limits of Schemes", registered `stacks-limits-of-schemes-a04446e5`): a closed subscheme of a
noetherian base that represents the agreement condition there, pulled back to `Spec R`, represents
it over `Spec R`. The affine statement it concludes specialises the published
`Langlands.AbelianScheme.RigidifiedClassesEqualizerClosedStatement`, derived from Stacks tags 0BDP
and 0BF0 (registered `stacks-picard-diagonal-seesaw-0bdp-0bf0-a04446e5`); the provenance of the
two hypotheses is described in their own Markdown files. The decomposition of the affine case into
these two hypotheses was chosen for task `e3d4a3ab-f378-42af-87c5-0cd4caec7b2e`.
