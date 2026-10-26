# Supplied p-adic specialization of residue normalization

For any universe `u`, prime `p`, `F : Langlands.PadicField.{u} p`, and explicitly
supplied `T : F.TopologicalData`, this module compares the general construction
in `Langlands.LocalField.ResidueNormalization` with the established host
normalization. All general objects use exactly `T.topology`, `T.valuativeRel`,
and `T.localField`, installed locally. There are no new global instances or
extra normalization hypotheses.

`Langlands.FML.Padic.ord_eq_host_ord_of_ne_zero` proves
`Langlands.FML.Padic.ord T x = (T.ord x : WithTop ℤ)` for `x ≠ 0`. It reuses
the existing supplied-data abbreviations `normalizedValuation` and `ord`
from `Langlands.LocalFactor.FML.Conductors`, together with
`normalizedValuation_eq_discreteValuation`. The proof applies the general
nonzero logarithm formula and unfolds only the public host order definition.
The comparison deliberately excludes zero: the FML order sends zero to `⊤`,
whereas `T.ord 0 = 0`. Both existing conventions are retained.

In `Langlands.PadicField.TopologicalData`,
`general_residueCardinality_eq` is definitional equality of the cardinalities
of the same actual residue field. The pointwise bridge
`residueNormalizedAbsoluteValue_eq_normalizedAbs` proves, for every `x`,
that the general bundled absolute value evaluates to `T.normalizedAbs x`.
Its nonzero case combines the finite-order formula, the preceding order
comparison, and the existing host nonzero formula. Its zero case uses
`AbsoluteValue.map_zero` and the existing `normalizedAbs_zero`.
The host multiplication, nonnegativity, zero criterion, ultrametric and
uniformizer laws are already proved in
`Langlands.LocalField.Normalization.Proof`; this module imports that proof
and adds only the comparison.

This bridge is an internal derived adapter for the normalization on David
Renard, *Représentations des groupes réductifs p-adiques*, French 9 July 2026
version, V.1, printed page 103 / PDF page 109, with context on printed
page 104 / PDF page 110. Registered source
`renard-2026-representations-groupes-reductifs-padiques`, SHA256
`7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`.
The Lean-specific comparison is derived from the two existing constructions;
it is not a separate theorem asserted in the source. The source normalization
and errata reading record are given in the companion
[general construction](ResidueNormalization.md).

This p-adic specialization does not restrict the general construction to
characteristic zero. No inverse-sign NYLL comparison, Haar result, or claim
about the remainder of V.1 is included. Worker 607 authored this adapter.
