# Coefficients after substituting `(X, 0)`: statement

This module defines
`Langlands.NYLL.PortInternal.M362.d001Statement.{u}`.
It is the proposition of NYLL source unit M362.001, the private theorem
`LubinTate.coeff_subst_X_zero`, at
`Nyll/ClassFieldTheory/LubinTate/FiniteLevel/PrimitiveDisplacement.lean:47–69`,
commit `fbd320cd8b1b06487c58227e92eb135794267709`.
The original file SHA-256 is
`520ab08231608ac43915d72c8a94c5d4ea1ad2fd4b7311a77f8f889a37421cbc`.
The registered source is `nyll-classfieldtheory-fbd320cd-supplement`,
content fingerprint
`a81005c3aceabc51e9193cdc643d4dd81dd9d496dca2a0cf0111ce610d5b0330`.
The retained source is under
`/home/taskhub/pilot/literature/External Lean project reuse survey- pinned source snapshots, 21 October 2026/n-yamaguchi-0729--ClassFieldTheory/source/`.

For any commutative ring `R : Type u`, bivariate formal power series `f`,
and exponent `d : Fin 2 →₀ ℕ` with `d 1 = 0`, the coefficient of degree
`d 0` in `f(X, 0)` equals the coefficient indexed by `d` in `f`.
The hypothesis is an explicit argument of the target, as it is in the
source theorem. The target adds no field, valuation, topology, local-field,
or Lubin–Tate hypothesis.

The changes are the `Langlands.NYLL.PortInternal.M362.d001Statement` name
for a source-private helper, an explicit name `u` for the source's
independent ring universe, replacement of the theorem by a Prop-valued
definition, `_hd` for the explicit hypothesis binder, omission of unused
outer local-field section variables, and reduction of imports to
`Mathlib.RingTheory.MvPowerSeries.Substitution` and
`Mathlib.RingTheory.PowerSeries.Basic`. No equality or mathematical
hypothesis has changed. The Lean header retains the original authorship
and Apache-2.0 notice; the Library carries
`licenses/NYLL/LICENSE` and `licenses/NYLL/NOTICE`.

This target is needed by M362.002, which proves divisibility of the
formal-group displacement by the second variable. It has no dependence
on the definition of the standard formal group. Mathlib supplies
`MvPowerSeries.subst`, `MvPowerSeries.coeff` and `PowerSeries.coeff`.
Its `MvPowerSeries.coeff_subst` is a general coefficient formula, rather
than this particular coefficient equality; no replacement of the exact
source unit is asserted here.

This module defines a statement target and contains no proof. Its proof is
routed to a separate `lean.proof@1` task after target publication. The pair
originates in Worker 299's shared draft for Task 6047; Worker 326 verified
the source correspondence and prepared it for submission.
