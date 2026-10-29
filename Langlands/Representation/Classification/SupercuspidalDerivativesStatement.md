# Derivatives of irreducible supercuspidal representations

Authors: Worker 758 (initial statement) and Worker 508 (source verification
and independent module layout), for task 8e5b4563-0365-41c7-b134-70f2a0b36292.

This module defines the unproved proposition
`Langlands.Classification.SupercuspidalDerivatives.{uF,uW} F T`. It is the
cuspidal part (a) of the six statements documented in
[SegmentSocleDerivativesStatement](SegmentSocleDerivativesStatement.md).
The remaining five propositions import this module; this module imports no
segment-socle definitions or statements.

## Source

I. N. Bernstein and A. V. Zelevinsky, *Induced representations of reductive
p-adic groups I* (1977), literature ID `bernstein-zelevinsky-1977-induced-i`,
SHA256 `8424600228ab72c5937e45edceefcae410a2a0b8f5ebf282185691542aa89092`,
§3.5 (printed p.452) and §4.3–4.4 (printed p.454; PDF index 14).
No applicable errata note was found in the registered public notes.

For irreducible cuspidal `ρ` of `GL_N`, BZ77 §4.4 states that the
intermediate positive derivatives vanish and the top derivative is
one-dimensional on `GL_0`. It cites Gelfand–Kazhdan for the mirabolic
restriction of a cuspidal representation and uniqueness of Whittaker models.
These citations locate the theorem; they do not provide its Lean proof.

## Exact statement

The outer telescope is
`{p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p) (T : F.TopologicalData)`.
The definition installs `letI := T.topology` and quantifies over every
continuous nontrivial unitary additive character `ψ`, every `n : ℕ`, and
`A : SmoothRep.{0,uF,uW} ℂ (GeneralLinear (n+1) F.Carrier)`.
Given `A.IsIrreducible` and
`GeneralLinear.IsSupercuspidal A.representation`, it asserts:

1. For all `k : ℕ` and `hk : k ≤ n+1`, if `0 < k < n+1`, then
   `Subsingleton ((Derivative.generalLinearDerivative T ψ (n+1) k hk).obj A)`.
2. `Module.finrank ℂ
   ((Derivative.generalLinearDerivative T ψ (n+1) (n+1) le_rfl).obj A) = 1`.

These are the two source assertions in BZ77 §4.4. The positive rank is
written `n+1`; `uW` is independent of the field universe `uF`. The supplied
topology is used throughout. The statement assumes no existence theorem for
`ψ`, introduces no level predicate, and uses actual derivative objects.

## Normalization and status

The public `Derivative.generalLinearDerivative` restricts to the mirabolic
subgroup, iterates `Mirabolic.phiMinus`, and applies `Mirabolic.psiMinus` for
positive orders; order zero is the identity. The minus functors use the
inverse-half determinant twist on the output group. BZ77 uses the
inverse-half Haar modulus of the conjugation action on the unipotent
radical. On the mirabolic Levi this modulus is `|det|`. The formal
comparison is separately assigned to statement task
a622f240-4846-4086-b34f-f650ba636ee4 and proof task
f947a735-872d-44db-a9ea-954d17dec4bd. A proof must establish that comparison
where used, or argue directly with the determinant normalization.

This contribution proves neither the two derivative assertions nor that
comparison. It declares one `Prop`-valued `def` with no additional theorem
premise. Its exact proof successor must use independently proved BZ77
inputs, not any segment derivative formula or segment classification result.

## Imports and independence

The direct imports are `Langlands.Representation.Classification.Supercuspidal`,
`Langlands.Representation.Derivative.Iteration` and
`Langlands.HarmonicAnalysis.Basic`. Their transitive `Langlands` closure at
Library base `9f141aa49982eab63f32f392c4c63dcb83837a19` contains
57 modules, with no segment-socle definitions, segment derivative
statements or segment classification conclusions. This lower placement
permits the BZ77-only upstream consumer to import this proposition without
importing the segment-socle part of the six-statement contribution. It does
not claim that any as-yet-unproved prerequisite is available as a theorem.
