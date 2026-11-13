# Evaluation admissibility for a pair: statement

This module defines `Langlands.NYLL.PortInternal.M362.d016Statement.{u}`.
Its exact source is NYLL M362.016, the private theorem
`LubinTate.hasEval_fin_two`, in
`Nyll/ClassFieldTheory/LubinTate/FiniteLevel/PrimitiveDisplacement.lean:274–284`
(statement at lines 274–278),
pinned commit `fbd320cd8b1b06487c58227e92eb135794267709`.
The original file SHA-256 is
`520ab08231608ac43915d72c8a94c5d4ea1ad2fd4b7311a77f8f889a37421cbc`.
The registered source is `nyll-classfieldtheory-fbd320cd-supplement`,
content fingerprint
`a81005c3aceabc51e9193cdc643d4dd81dd9d496dca2a0cf0111ce610d5b0330`.
The retained source root is
`/home/taskhub/pilot/literature/External Lean project reuse survey- pinned source snapshots, 21 October 2026/n-yamaguchi-0729--ClassFieldTheory/source/`.

For any commutative ring `R : Type u` with a topological space structure,
and any two points `x y : R` satisfying `PowerSeries.HasEval` individually,
the target asserts `MvPowerSeries.HasEval (![x, y] : Fin 2 → R)`.
It imposes no continuity, Hausdorffness, completeness, field, valuation,
or local-field hypotheses. Both individual admissibility proofs remain
explicit arguments, exactly as in the source.

The changes are the namespace/name
`Langlands.NYLL.PortInternal.M362.d016Statement` for the private helper,
the explicit name `u` for its independent source ring universe,
replacement of the theorem by a Prop-valued definition, `_hx` and `_hy`
for hypothesis binder names, omission of unused enclosing local-field
section variables and instances, and replacement of the external imports
by `Mathlib.RingTheory.PowerSeries.Evaluation`. The Lean header retains
original authorship and Apache-2.0 notices; the Library carries
`licenses/NYLL/LICENSE` and `licenses/NYLL/NOTICE`.

M362.018 uses this helper to evaluate a bivariate formal-group displacement
factor at two topologically nilpotent level-field integers. The present
statement has no dependence on that formal group or level field.
`PowerSeries.HasEval` and `MvPowerSeries.HasEval` are the Mathlib notions;
the latter requires componentwise topological nilpotence and convergence
along the cofinite filter. This finite-pair result is the specialized
source unit, rather than a replacement for the general definitions.

This module supplies the statement target. Its exact proof is a separate
publication after the target is integrated. The approved environment is
`5c94c648-e8dc-4002-a50a-071ebf3f6096`, Lean 4.34.0 with Mathlib
`5ed2965256430c3649e86755f9576b54eca72435`.
