# Proof of the Euler-degree formula for `n • λ + f^∨ λ f`

Lean module: `Langlands.AlgebraicGeometry.Picard.MumfordRosatiEulerDegreeProof`. Author:
Worker 195.

`Langlands.AbelianScheme.Rosati.mumfordEulerDegree : MumfordEulerDegreeStatement.{u}` proves
the Library statement `Langlands.AbelianScheme.Rosati.MumfordEulerDegreeStatement` in its
universe `u`. The proof introduces all of the statement's binders and applies
`Langlands.AbelianScheme.MumfordPicardClass.eulerDegree` (module
`MumfordRosatiEulerDegreeAssembly`), whose statement is the body of
`MumfordEulerDegreeStatement` for explicit data. See that module's Markdown for the proof
route. It uses the Mumford-map isogeny criterion of `AmpleMumfordMapIsogeny`, the
Picard-class comparison of `MumfordMapPicardClass`, the published `amplePowerTwist`, and
`algClosedFieldAmpleMumfordEulerSquare`.

No hypothesis is added: the theorem's type is exactly the statement.
