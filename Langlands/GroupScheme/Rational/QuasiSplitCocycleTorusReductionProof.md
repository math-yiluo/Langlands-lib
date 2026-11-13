# Torus reduction for cocycles of quasi-split semisimple groups

Authors: Worker 4767.

Lean module: `Langlands.GroupScheme.Rational.QuasiSplitCocycleTorusReductionProof`, namespace
`Langlands.GroupScheme`.

This module proves `QuasiSplitCocycleTorusReductionStatement.{u}` (module
`Rational/QuasiSplitCocycleTorusReductionStatement`) for an arbitrary universe `u`. That
statement says the following. Take a field `K : Type u`, a semisimple quasi-split group scheme
`G` over `K`, a finite Galois extension `L/K` in `Type u` and a natural cocycle `ξ` of `G` on
`Spec L → Spec K`. Then there is a `Cocycle.TorusReduction ξ`. Such a reduction consists of a
finite Galois refinement in `Type u` with an fpqc refinement morphism, a cochain and a closed
`K`-torus of `G`. The twisted refined cocycle factors through that torus on every test over
`Spec K`. The module chains published Library theorems. Every hypothesis of the chain has a
published proof, so the closing theorem has no premises.

## Declarations

All four are theorems in namespace `Langlands.GroupScheme` with conclusion
`QuasiSplitCocycleTorusReductionStatement.{u}`.

- `quasiSplitCocycleTorusReduction_of_regularConjugate`, with hypothesis
  `hconj : QuasiSplitSimplyConnectedRegularConjugateStatement.{u}` (module
  `Rational/QuasiSplitRegularConjugateStatement`). That statement is Steinberg's §10 step. Start
  with a rational point of an inner twist of a simply connected quasi-split group whose
  centralizer lies in a torus. The statement transfers it to such a rational point of the
  quasi-split group itself, together with a closed torus containing the centralizer and a
  conjugating point over a finite Galois extension.
- `quasiSplitCocycleTorusReduction_of_classRational`, with hypothesis
  `hclass : QuasiSplitRegularClassRationalStatement.{u}` (module
  `Rational/QuasiSplitRegularClassRationalStatement`). That is Borel–Springer 8.6 for
  Galois-stable strongly regular classes of simply connected quasi-split groups.
- `quasiSplitCocycleTorusReduction_of_steinbergQuotient`, with hypothesis
  `hquot : QuasiSplitSteinbergQuotientStatement.{u}` (module
  `Rational/QuasiSplitSteinbergQuotientStatement`). That is Steinberg's class quotient of a
  simply connected quasi-split group.
- `quasiSplitCocycleTorusReduction : QuasiSplitCocycleTorusReductionStatement.{u}`, the
  closing theorem, without hypotheses.

## Proof

The first theorem uses the Library theorem `quasiSplitCocycleTorusReduction_of_prerequisites`
(module `Rational/QuasiSplitCocycleTorusReduction`). It proves
`QuasiSplitCocycleTorusReductionPrerequisitesStatement.{u}`, the implication
`SimplyConnectedCoverExistenceStatement → InfiniteFieldStronglyRegularPointStatement →
QuasiSplitSimplyConnectedRegularConjugateStatement → QuasiSplitCocycleTorusReductionStatement`.
That theorem treats finite fields by Lang's theorem. For infinite fields it takes the twist,
form, stabilizer-torus and quasi-split-lift inputs from their published proofs. The first
theorem applies it to three arguments:

- `simplyConnectedCoverExistence` (module `SimplyConnected/CoverExistenceProof`): every
  semisimple group over a field has a simply connected central cover;
- `infiniteFieldStronglyRegularPoint` (module `Rational/InfiniteFieldStronglyRegularPoint`):
  a connected reductive group over an infinite field has a rational point whose all-test
  centralizer lies in a closed torus;
- the hypothesis `hconj`.

The second theorem applies the first to
`quasiSplitSimplyConnectedRegularConjugate_of_classRational hclass regularConjugateFiniteGalois`.
The function `quasiSplitSimplyConnectedRegularConjugate_of_classRational` (module
`Rational/QuasiSplitRegularConjugateReduction`) is the published reduction of the conjugacy
transfer to two statements, `QuasiSplitRegularClassRationalStatement` and
`RegularConjugateFiniteGaloisStatement`. The theorem `regularConjugateFiniteGalois` (module
`Rational/RegularConjugateFiniteGaloisProof`) is the published proof of the second.

The third theorem applies the second to `quasiSplitRegularClassRationalReduction hquot`. Here
`quasiSplitRegularClassRationalReduction` (module `Rational/QuasiSplitRegularClassRationalReduction`)
is the published proof of `QuasiSplitSteinbergQuotientStatement →
QuasiSplitRegularClassRationalStatement`.

The closing theorem `quasiSplitCocycleTorusReduction` applies the third theorem to
`quasiSplitSteinbergQuotient` (module `Rational/QuasiSplitSteinbergQuotient`), the published
proof of `QuasiSplitSteinbergQuotientStatement.{u}`. That proof takes as witnesses the
canonical class-function quotient `ClassFunctions.quotient G` and the map
`ClassFunctions.rho G`. It obtains the three required properties from
`ClassFunctions.rho_conjugation`, `ClassFunctions.stronglyRegularFibres` and
`ClassFunctions.stronglyRegularRationalLifting`.

The whole construction stays inside the target's terms. The four theorems take the field `K`,
the universe `u`, the group `G`, the extension `L/K` and the cocycle `ξ` exactly as the target
quantifies them. They add no hypothesis on dimension, norms, perfectness or characteristic.
The finite Galois refinement, fpqc refinement morphism, cochain, closed `K`-torus and all-test
factorization are the ones built by `quasiSplitCocycleTorusReduction_of_prerequisites`.

The closing theorem uses only `propext`, `Classical.choice` and `Quot.sound`.

## Sources and provenance

Provenance: internal. The module only applies existing Library theorems and formalizes no
separate literature statement. The argument as a whole is that of R. Steinberg, *Regular
elements of semi-simple algebraic groups* (1965), source
`steinberg-1965-regular-elements-semisimple-groups`, SHA-256
`bda20c4a4b3cf4a7e9e5b17a4eacd0147d0c9370063ab3a3778114a53c8349b9`, §10 (printed p.78, PDF p.31)
and §11 (printed p.79, PDF p.32). Steinberg assumes a perfect field. The extension to
arbitrary fields is due to A. Borel and T. A. Springer, *Rationality properties of linear
algebraic groups II* (1968), source `borel-springer-1968-rationality-properties-ii`, SHA-256
`e465d0622ca9540ff21e0d53d7b2fdb00a14cf70a7caceee352c040a3cb1abef`, §8.6 (printed pp.483–484,
PDF pp.41–42). The Lean proof does not use 8.6 as a premise. In this development the
arbitrary-field case comes from the published proofs named above, and their modules
document how they relate to these sources.
