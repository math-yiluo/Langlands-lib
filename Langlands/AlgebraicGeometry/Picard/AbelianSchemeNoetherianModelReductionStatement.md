# Noetherian models from abelian-scheme and line-bundle descent

`Langlands.AbelianScheme.AbelianSchemeNoetherianModelReductionStatement.{u}` is the proposition

```lean
Langlands.AbelianScheme.SubalgebraDescentStatement.{u} →
  LineBundleSubalgebraDescentStatement.{u} →
    LineBundleIsoSubalgebraDescentStatement.{u} →
      AbelianSchemeNoetherianModelStatement.{u}
```

in module `Langlands.AlgebraicGeometry.Picard.AbelianSchemeNoetherianModelReductionStatement`,
with `open Langlands.AlgebraicGeometry.NoetherianApproximation`. This unit only defines the
proposition. It proves nothing, in particular none of the four named propositions. It says
only that the last follows from the first three.

## The four propositions

All four are existing Prop-valued definitions of the Library, used unchanged at the same
universe `u`.

- `Langlands.AbelianScheme.SubalgebraDescentStatement` (module
  `Langlands.AbelianScheme.SubalgebraDescentStatements`), the first hypothesis. Every abelian
  scheme `A` over `Spec R` is isomorphic, in `AbelianScheme (Spec R)`, to the base change of an
  abelian scheme over `Spec R₀` for a finitely generated subring `R₀ : Subalgebra ℤ R`.
- `LineBundleSubalgebraDescentStatement` (module
  `Langlands.AlgebraicGeometry.NoetherianApproximation.LineBundleDescentStatements`), the second
  hypothesis. Let `X₀` be quasi-compact and quasi-separated over `Spec A₀`, and let `X` be its base
  change to `Spec A`, given by a pullback square. Every locally free rank-one module on `X` is
  isomorphic to the pullback of such a module on the chosen base change of `X₀` to `Spec T`, for a
  finitely generated `A₀`-subalgebra `T` of `A` containing a given finite set.
- `LineBundleIsoSubalgebraDescentStatement` (same module), the third hypothesis. Two locally free
  rank-one modules on such an `X₀` whose pullbacks to `X` are isomorphic already have isomorphic
  pullbacks on every base change of `X₀` to `Spec T`, for such a `T`.
- `Langlands.AbelianScheme.AbelianSchemeNoetherianModelStatement` (module
  `Langlands.AlgebraicGeometry.Picard.AbelianSchemeNoetherianModelStatement`), the conclusion.
  Let `A` be an abelian scheme over `Spec R` with two line bundles `M₁`, `M₂` on `A.X.left`, each
  rigidified along `unitSection A`. Then there are a noetherian ring `R₀`, a ring map
  `φ : R₀ ⟶ R`, an abelian scheme `A₀` over `Spec R₀` and a map `a : A.X.left ⟶ A₀.X.left` such
  that `a` forms a pullback square over `Spec.map φ` and carries the unit section of `A` to
  that of `A₀`. There are also two rigidified line bundles on `A₀.X.left` whose underlying line
  bundles pull back along `a` to those of `M₁` and `M₂`.

## Provenance

Internal. The implication is a decomposition step of proof task
`a825ba6f-ac5b-43b7-8794-52b2039388f7` and adds no mathematics of its own. It is the standard
assembly behind the conclusion's Markdown. Descend `A` to a finitely generated subring. Then
descend each line bundle with the second hypothesis, enlarging the subring each time. Finally
descend, with the third hypothesis applied on the base, the isomorphism between the pullback of
each descended bundle along the unit section and the structure sheaf. That isomorphism exists
after base change to `Spec R` because `M₁` and `M₂` are rigidified. Finitely generated
`ℤ`-algebras are noetherian. The geometric input is in the three hypotheses, whose Markdown
cites the Stacks Project, Chapter 32 *Limits of Schemes* (tags 01ZM, 01ZR, 0B8W and the property
descents). A Lean proof of the implication is a separate unit.
