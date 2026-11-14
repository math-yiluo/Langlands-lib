# Proof of Conrad's Theorem 4.5 on actual adelic points

Author: Worker 245. Worker 3519 supplied the composition in the task context.

`Langlands.Global.adelicSpreadSmoothOpen` proves the unchanged published
`Langlands.Global.AdelicSpreadSmoothOpenStatement.{u}` for every universe `u`.
The theorem has no additional premise.

The source is Brian Conrad, *Weil and Grothendieck approaches to adelic
points*, December 31, 2011, Theorem 4.5 and its proof on printed pp.12–13.
Registered source: `conrad-2011-weil-grothendieck-adelic-points`, PDF SHA-256
`fe4a9193aff4ef575665b40971f3da32f850a74d87b3f2d0fa28bba26b9cbabb`.

The statement concerns a smooth surjective morphism with geometrically
connected fibres between separated generic fibres over a global field.
The induced map on actual adelic points is open for the topologies supplied
by any finite-type spreads of its source and target. Its function-field
branch has finite constant field; its number-field branch uses full adeles,
including every infinite place. The source and target spreads and their
finite sets of places are independently quantified. The statement imposes
no common fibre dimension.

The implemented proof is the application

```lean
adelicSpreadSmoothOpenOfLangWeil Langlands.AlgebraicGeometry.uniformLangWeil
```

The first imported module,
`Langlands.Global.AdelicSpreadSmoothOpenOfLangWeilProof`, proves
`AdelicSpreadSmoothOpenOfLangWeilStatement.{u}`, which is the implication
from `Langlands.AlgebraicGeometry.UniformLangWeilStatement.{u}` to the
target. Its two branches assemble compatible smooth geometrically connected
models, local openness, almost-all integral surjectivity and the reduction
from those models to the arbitrary spreads in the statement. These
implement Conrad's local-product and henselian-lifting argument.

The second imported module,
`Langlands.AlgebraicGeometry.UniformLangWeilProof`, supplies that entire
premise through the published theorem `uniformLangWeil.{u}`. Its proof
composes `LangWeil.uniformLangWeilOfFamily` with
`LangWeil.familyLangWeilOfPlaneCurve LangWeil.planeCurveHasseWeil`, in
namespace `Langlands.AlgebraicGeometry`. Thus the uniform estimate of
Conrad's Lemma 4.6 is discharged by the published elementary Lang–Weil
proof through a plane-curve bound and dimension induction. This uses the
implemented elementary route in place of the cohomological proof described
by Conrad.

This module's derived content is the composition of those two published
proofs in the same arbitrary universe. It leaves the target pair and its
imported definitions unchanged and introduces no auxiliary assumption.
