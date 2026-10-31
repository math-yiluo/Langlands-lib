# Proof: noetherian approximation of the agreement of two rigidified classes

`Langlands.AbelianScheme.rigidifiedClassesNoetherianApproximation` proves
`Langlands.AbelianScheme.RigidifiedClassesNoetherianApproximationStatement.{u}`, stated in
`Langlands/AlgebraicGeometry/Picard/RigidifiedClassesNoetherianApproximationStatement.lean`.
See that module's Markdown for the statement and its source. In short: take an abelian scheme
`A` over `Spec R` with two rigidified classes `q` and `r`. There are a noetherian ring `R₀`, a
map `φ : R₀ ⟶ R`, an abelian scheme `A₀` over `Spec R₀` and two classes `q₀`, `r₀` with the
following property. For every test object `T'` over `Spec R`, the pullbacks of `q` and `r` to
`T'` agree exactly when the pullbacks of `q₀` and `r₀` to `T'` agree, where `T'` lies over
`Spec R₀` through `Spec.map φ`.

The module has no new mathematics. Its one declaration composes proved implications with the
proofs of their hypotheses, as a single term.

## The composition

```lean
rigidifiedClassesNoetherianApproximationReduction
  (abelianSchemeNoetherianModelReduction
    (subalgebraDescentReduction schemeSubalgebraDescent GroupScheme.subalgebraDescent
      isSeparatedSubalgebraDescent isProperSubalgebraDescent smoothSubalgebraDescent
      geometricallyConnectedSubalgebraDescent)
    lineBundleSubalgebraDescent lineBundleIsoSubalgebraDescent)
```

All names are in `Langlands.AbelianScheme`, or in
`Langlands.AlgebraicGeometry.NoetherianApproximation` (opened), or in `Langlands.GroupScheme`
(written `GroupScheme.subalgebraDescent`).

1. **Approximation from noetherian models.**
   `rigidifiedClassesNoetherianApproximationReduction`
   (`RigidifiedClassesNoetherianApproximationReductionProof`) proves
   `RigidifiedClassesNoetherianApproximationReductionStatement.{u}`:
   `AbelianSchemeNoetherianModelStatement.{u}` implies the target. It is applied to a proof of
   the model statement.
2. **Noetherian models.** `abelianSchemeNoetherianModelReduction`
   (`AbelianSchemeNoetherianModelProof`) proves
   `AbelianSchemeNoetherianModelReductionStatement.{u}`. Abelian-scheme descent
   (`Langlands.AbelianScheme.SubalgebraDescentStatement.{u}`), line-bundle descent
   (`LineBundleSubalgebraDescentStatement.{u}`) and descent of isomorphisms of line bundles
   (`LineBundleIsoSubalgebraDescentStatement.{u}`) together imply
   `AbelianSchemeNoetherianModelStatement.{u}`.
3. **Abelian-scheme descent.** `subalgebraDescentReduction`
   (`Langlands/AbelianScheme/SubalgebraDescentProof.lean`) proves
   `SubalgebraDescentReductionStatement.{u}`. It derives
   `Langlands.AbelianScheme.SubalgebraDescentStatement.{u}` from six descent statements, given
   in this order:
   scheme descent (`SchemeSubalgebraDescentStatement`), group-law descent
   (`Langlands.GroupScheme.SubalgebraDescentStatement`), and descent of separatedness
   (`IsSeparatedSubalgebraDescentStatement`), properness (`IsProperSubalgebraDescentStatement`),
   smoothness (`SmoothSubalgebraDescentStatement`) and geometric connectedness
   (`GeometricallyConnectedSubalgebraDescentStatement`).
4. **The eight descent statements.** Each one is proved by its own theorem, which bridges a
   ported FLT theorem to the Library statement:

   | Statement | Theorem | Module |
   | --- | --- | --- |
   | `SchemeSubalgebraDescentStatement` | `schemeSubalgebraDescent` | `NoetherianApproximation/SchemeSubalgebraDescentProof` |
   | `GroupScheme.SubalgebraDescentStatement` | `GroupScheme.subalgebraDescent` | `AbelianScheme/GroupSchemeSubalgebraDescentProof` |
   | `IsSeparatedSubalgebraDescentStatement` | `isSeparatedSubalgebraDescent` | `NoetherianApproximation/IsSeparatedSubalgebraDescentProof` |
   | `IsProperSubalgebraDescentStatement` | `isProperSubalgebraDescent` | `NoetherianApproximation/IsProperSubalgebraDescentProof` |
   | `SmoothSubalgebraDescentStatement` | `smoothSubalgebraDescent` | `NoetherianApproximation/SmoothSubalgebraDescentProof` |
   | `GeometricallyConnectedSubalgebraDescentStatement` | `geometricallyConnectedSubalgebraDescent` | `NoetherianApproximation/GeometricallyConnectedSubalgebraDescentProof` |
   | `LineBundleSubalgebraDescentStatement` | `lineBundleSubalgebraDescent` | `NoetherianApproximation/LineBundleSubalgebraDescentProof` |
   | `LineBundleIsoSubalgebraDescentStatement` | `lineBundleIsoSubalgebraDescent` | `NoetherianApproximation/LineBundleIsoSubalgebraDescentProof` |

   The first, third to sixth and last two are stated in the Library modules
   `Langlands.AlgebraicGeometry.NoetherianApproximation.SubalgebraDescentStatements` and
   `Langlands.AlgebraicGeometry.NoetherianApproximation.LineBundleDescentStatements`. The group-law
   statement is in `Langlands.AbelianScheme.SubalgebraDescentStatements`. The Markdown of each
   proof module describes its bridge and the Stacks Project source of its statement.

The universe parameter `u` is the same throughout. Every implication is stated for an arbitrary
universe, so no universe lifting is needed.

## Imports

The module imports the three reduction proofs (steps 1–3) and the eight descent proofs (step 4).
Each descent proof imports its ported FLT modules under `Langlands.AnthropicFLT.*`; this module
uses only the bridge theorems named above.

## Checks

The eight descent proofs of step 4 are all in the Library (commit `91ab820b`). Over that Library,
`lean_check` `b02d7c56` compiles this module and the four helper modules it adds
(`SubalgebraDescentReductionStatement`, `SubalgebraDescentProof`,
`AbelianSchemeNoetherianModelProof`, `RigidifiedClassesNoetherianApproximationReductionProof`)
with 0 errors and 0 warnings. The same check shows that
`Langlands.AbelianScheme.rigidifiedClassesNoetherianApproximation` depends only on the axioms
`propext`, `Classical.choice` and `Quot.sound`.
