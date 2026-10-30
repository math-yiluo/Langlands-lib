# Reduction of noetherian approximation of agreement to noetherian models

`Langlands.AbelianScheme.RigidifiedClassesNoetherianApproximationReductionStatement.{u}` is the
proposition

```lean
AbelianSchemeNoetherianModelStatement.{u} →
  RigidifiedClassesNoetherianApproximationStatement.{u}
```

It lives in module
`Langlands.AlgebraicGeometry.Picard.RigidifiedClassesNoetherianApproximationReductionStatement`.
This unit only defines the proposition. It proves nothing. In particular it proves neither
of the two named propositions. It only says that the second follows from the first.

## The two propositions

Both are Prop-valued definitions in `namespace Langlands.AbelianScheme`, used unchanged at the
same universe `u`.

- `AbelianSchemeNoetherianModelStatement.{u}` (module
  `Langlands.AlgebraicGeometry.Picard.AbelianSchemeNoetherianModelStatement`), the
  hypothesis. For every commutative ring `R`, abelian scheme `A` over `Spec R` and two line
  bundles `M₁`, `M₂` on `A.X.left` rigidified along `unitSection A`, there are a noetherian
  `R₀ : CommRingCat.{u}`, a ring map `φ : R₀ ⟶ R`, an abelian scheme `A₀` over `Spec R₀`, a
  morphism `a : A.X.left ⟶ A₀.X.left` with `IsPullback a A.X.hom A₀.X.hom (Spec.map φ)` and
  `unitSection A ≫ a = Spec.map φ ≫ unitSection A₀`, and two rigidified line bundles `M₁₀`,
  `M₂₀` on `A₀.X.left` whose underlying line bundles pull back along `a` to bundles isomorphic
  to the underlying line bundles of `M₁` and `M₂`.
- `RigidifiedClassesNoetherianApproximationStatement.{u}` (module
  `Langlands.AlgebraicGeometry.Picard.RigidifiedClassesNoetherianApproximationStatement`), the
  conclusion. For every commutative ring `R`, abelian scheme `A` over `Spec R` and two
  rigidified classes `q r : RigidifiedClasses A (Over.mk (𝟙 (Spec R)))`, there are a noetherian
  `R₀ : CommRingCat.{u}`, a ring map `φ : R₀ ⟶ R`, an abelian scheme `A₀` over `Spec R₀` and two
  classes `q₀ r₀ : RigidifiedClasses A₀ (Over.mk (𝟙 (Spec R₀)))` such that, for every test
  object `T'` over `Spec R` and every `h : T' ⟶ Over.mk (𝟙 (Spec R))`, the pullbacks of `q` and
  `r` along `h` are equal exactly when the pullbacks of `q₀` and `r₀` along
  `Over.homMk (T'.hom ≫ Spec.map φ) : Over.mk (T'.hom ≫ Spec.map φ) ⟶ Over.mk (𝟙 (Spec R₀))`
  are equal.

So the proposition says: if every abelian scheme over an affine base, together with two
rigidified line bundles on its total space, has a model over a noetherian ring in the above
weak sense, then agreement of two rigidified classes is detected over a noetherian ring.

## Provenance

Internal. The implication is a decomposition step of this project, made in proof task
`a825ba6f-ac5b-43b7-8794-52b2039388f7` for the published conclusion. It adds no mathematics
of its own: the conclusion's paired Markdown already explains that it is expected to follow
from base change of `A`, `q` and `r` from a noetherian model, and the hypothesis is exactly
that model. The geometric input (noetherian descent, Stacks Project Chapter 32) is in the
hypothesis; see its paired Markdown. A Lean proof of the implication is a separate unit.
