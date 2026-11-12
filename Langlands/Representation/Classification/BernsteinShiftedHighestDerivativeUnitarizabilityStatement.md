# Unitarizability of the shifted highest derivative

Worker 4876. This module states
`Langlands.Classification.BernsteinShiftedHighestDerivativeUnitarizability.{uF, uV} F T`.
It is a Prop-valued definition. **Nothing is proved here**, and no result is
assumed.

## Statement

Fix `{p : ℕ} [Fact p.Prime]`, `F : PadicField.{uF} p` and
`T : F.TopologicalData`. The statement installs `letI := T.topology`. The field
universe `uF` and the representation universe `uV` are independent.

`BernsteinShiftedHighestDerivativeUnitarizability F T` says the following. Take
any `N` with `0 < N`, any unitary additive character
`ψ : @UnitaryAdditiveCharacter F.Carrier _ T.topology`, and any actual smooth
complex representation
`π : SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear N F.Carrier)` that is
irreducible (`Representation.IsIrreducible`) and unitarizable
(`IsUnitarizable`). Then for every
`hd : Derivative.GeneralLinearHighestDerivativeOrderData T ψ π`, the
representation `shiftedHighestDerivative F T ψ hd` of `GL_(N - hd.order)` is
unitarizable.

This is word for word the second conjunct of the conclusion of
`Langlands.Classification.BernsteinShiftedHighestDerivativeUnitarity` in
`Classification/BernsteinUnitaryStatement.lean`, with the same binders and
hypotheses. That statement asserts that the shifted highest derivative is
irreducible *and* unitarizable. This one keeps only unitarizability. So
`BernsteinShiftedHighestDerivativeUnitarity F T` implies this statement
immediately. Conversely, this statement together with the irreducibility of
the shifted highest derivative gives `BernsteinShiftedHighestDerivativeUnitarity F T`.

## Library notions

All are used by Lean name. Their meaning and normalization are recorded in
`Classification/BernsteinUnitaryStatement.md` (sections "Part 3" and "The twist
exponent"), and are not changed here.

- `shiftedHighestDerivative F T ψ hd` (from `BernsteinUnitaryStatement`)
  unfolds to
  `T.segmentFactor ((Derivative.generalLinearDerivative T ψ N hd.order hd.le_rank).obj π) (1 / 2)`.
  This is `ν^(1/2) π^(h)` with `h = hd.order`, where
  `ν^(1/2)(g) = |det g|^(1/2)`.
- `Derivative.generalLinearDerivative T ψ N k hk` is, for `k ≥ 1`, restriction
  to the mirabolic `P_N`, then `(Φ⁻)^(k-1)`, then `Ψ⁻`, with the
  Bernstein-Zelevinsky normalized minus functors.
- `GeneralLinearHighestDerivativeOrderData T ψ π` records a positive order
  `k ≤ N` whose derivative is nonzero (`Nontrivial`), with every derivative of
  higher order `j ≤ N` zero (`Subsingleton`). So `hd.order` is the depth `h`
  of `π` and `π^(h)` is its highest derivative.
- `IsUnitarizable` (`Unitary.Basic`): existence of an invariant positive
  definite Hermitian form on the carrier, with no completion or topology.

## Source

J. N. Bernstein, *P-invariant distributions on GL(N) and the classification of
unitary representations of GL(N) (non-archimedean case)*, LNM 1041 (1984),
50–102. Registered as `bernstein-1984-p-invariant`, at
`/home/taskhub/central-library/Bernstein--P-invariant distributions on GL(N) and the classification of unitary representations of GL(N) (Non-archimedean case)--1983.pdf`,
SHA-256 `b050423087ee36592c4747ba6f3c9a9fdef9c8e4b8919e3737cf7ecdfcc94ab2`.
The PDF page is the printed page minus 49.

- §7.2, printed p.82 (PDF page 33): the depth `h`, the highest derivative
  `π^(h)`, and the shifted derivatives `π^[k] = ν^(1/2) · π^(k)` with
  `ν^(1/2)(g) = |det g|^(1/2)`.
- §7.4, printed p.83 (PDF page 34), "Unitarizability criterion for G-modules":
  a smooth irreducible representation `π` of `G` is unitarizable if and only if
  (i) `π` is Hermitian, (ii) the highest shifted derivative `π^[h]` is a
  unitarizable representation of `G_(n-h)`, and (iii) `π` is P-positive. The
  statement here is the "only if" direction for condition (ii).

Marko Tadic, *Classification of unitary representations in irreducible
representations of general linear group (non-archimedean case)*, Ann. Sci. ENS
(4) 19 (1986), 335–382. Registered as `tadic-1986-unitary`, at
`/home/taskhub/central-library/Tadic--Classification of unitary representations in irreducible representations of GL(n)--1986.pdf`,
SHA-256 `08e4e1e7c1ccc1e340999287867bc0448f3d8f4bab49906fbf1deda866ae4683`.
Theorem 2.5(iii), printed p.346 (PDF page 13): "If `π ∈ Irr^u` then
`π' ∈ Irr^u`", where `π'` is the highest shifted derivative of §1.16. The
statement here is the unitarizability part of that conclusion.

The rendered text of Bernstein pp.82–83 and Tadic p.346 was checked. No errata
entry for either source was found in the public notes.

## Formulation choices

The choices are those of `BernsteinShiftedHighestDerivativeUnitarity`, and are
explained in `Classification/BernsteinUnitaryStatement.md`: quantification over
every `ψ` and every `hd`, the hypothesis `0 < N` (which also follows from
`hd.positive` and `hd.le_rank`), the case `hd.order = N` (a representation of
`GL_0`), and the exponent `+1/2` of the shift, checked there on the trivial
representation of `GL_2`.

This statement is separated from the irreducibility half because the two
halves need different inputs. The intended proof of the unitarizability half
uses the unitarity of normalized `Φ⁻`
(`Langlands.Derivative.MirabolicPhiMinusUnitarity`, Bernstein §9.3(ii)) and
highestness; the irreducibility half needs Zelevinsky 1980, Theorem 8.1
(`Langlands.Derivative.GeneralLinearHighestDerivativeIrreducibility`). Both
are proof obligations outside this module.
Bernstein's §7.4 hypotheses include irreducibility of `π`, and the statement
keeps that hypothesis.
