# Abelian-scheme descent from scheme, group-law and property descent

`Langlands.AbelianScheme.SubalgebraDescentReductionStatement.{u}` is the proposition

```lean
SchemeSubalgebraDescentStatement.{u} →
  GroupScheme.SubalgebraDescentStatement.{u} →
    IsSeparatedSubalgebraDescentStatement.{u} →
      IsProperSubalgebraDescentStatement.{u} →
        SmoothSubalgebraDescentStatement.{u} →
          GeometricallyConnectedSubalgebraDescentStatement.{u} →
            Langlands.AbelianScheme.SubalgebraDescentStatement.{u}
```

in module `Langlands.AbelianScheme.SubalgebraDescentReductionStatement`, with
`open Langlands.AlgebraicGeometry.NoetherianApproximation`. This unit only defines the
proposition. It proves none of the seven named propositions. It says only that the last
follows from the first six.

## The propositions

All seven are existing Prop-valued definitions of the Library, used unchanged at the same
universe `u`.

- `SchemeSubalgebraDescentStatement`, `IsSeparatedSubalgebraDescentStatement`,
  `IsProperSubalgebraDescentStatement`, `SmoothSubalgebraDescentStatement` and
  `GeometricallyConnectedSubalgebraDescentStatement` are in module
  `Langlands.AlgebraicGeometry.NoetherianApproximation.SubalgebraDescentStatements`. The first
  descends a quasi-compact, quasi-separated morphism of finite presentation to `Spec A` to such a
  morphism to `Spec T`, through a pullback square. Here `T` is a finitely generated
  `A₀`-subalgebra of `A` containing a given finite set. The other four say that, for a morphism to
  `Spec A₀` under their stated hypotheses, the property of its base change to `Spec A` already
  holds for its base change to `Spec T`, for such a `T`. The properness and geometric
  connectedness ones assume `A₀` noetherian.
- `GroupScheme.SubalgebraDescentStatement` (module
  `Langlands.AbelianScheme.SubalgebraDescentStatements`) descends a group scheme whose
  underlying scheme is a base change of a quasi-compact, quasi-separated `X₀` of finite
  presentation over `Spec A₀`. The result is a group scheme over `Spec T` whose underlying scheme
  is a base change of `X₀`, commutative when the original one is, and whose base change to
  `Spec A` is isomorphic to the original one as a group scheme.
- `Langlands.AbelianScheme.SubalgebraDescentStatement` (same module), the conclusion. Every
  abelian scheme over `Spec R` is isomorphic, in `AbelianScheme (Spec R)`, to the base change of
  an abelian scheme over `Spec R₀` for a finitely generated subring `R₀ : Subalgebra ℤ R`.

## Provenance

Internal. The implication is a decomposition step of proof task
`a825ba6f-ac5b-43b7-8794-52b2039388f7` and adds no mathematics of its own. It is the assembly
described in the conclusion's Markdown. Descend the underlying scheme over the prime subring,
then the group law. Then descend separatedness, properness, smoothness and geometric
connectedness in turn, base-changing the descended group scheme at each step. Finitely generated
`ℤ`-algebras are noetherian, which the properness and connectedness steps need. The geometric
input is in the six hypotheses, whose Markdown cites the Stacks Project, Chapter 32 *Limits of
Schemes*. The implication is proved by `Langlands.AbelianScheme.subalgebraDescentReduction` in
module `Langlands.AbelianScheme.SubalgebraDescentProof`.
