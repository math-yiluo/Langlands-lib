# Concrete principal units as an antitone filtration

`Langlands.NYLL.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.toPrincipalUnitFiltration`
packages the concrete higher principal-unit subgroups as the published
`Langlands.NYLL.LocalFieldTheory.DiscreteValuationField.AntitoneSubgroupFiltration`.
Its parameters are `{K : Type u} [Field K]` and an explicit complete
valuation-field package `F : CompleteDVF.{u, v} K`. The result is a value of
the structure type `AntitoneSubgroupFiltration F.valuationSubringˣ : Type u`
(data, not a proposition), with subgroup at `n` definitionally the shared
`higherPrincipalUnitGroup F n`. Independent field and value-group universes,
parameter order and explicitness agree with the source. No new instances
are introduced.

For `m ≤ n`, membership at level `n` means membership of the unit's difference
from one in `F.maximalIdeal ^ n`. Mathlib's `Ideal.pow_le_pow_right` puts that
difference in `F.maximalIdeal ^ m`, giving the structure's antitone law.
This implements the original structure while replacing the source theorem
`higherPrincipalUnitGroup.antitone` (M225.003) directly with Mathlib. The
focused module therefore needs no separately published copy of that theorem.
The abstract filtration is reused by Lean name from
`Langlands.NYLL.ValuedFieldTheory.LocalField.DiscreteValuationField.Units.Filtration`;
the concrete subgroups are imported from the canonical M225.001 module.

The source is Naganori Yamaguchi's NYLL M231.020,
`Nyll/ValuedFieldTheory/LocalField/DiscreteValuationField/PrincipalUnits/Core.lean:384–387`,
with section parameters at lines 29–40, pinned commit
`fbd320cd8b1b06487c58227e92eb135794267709`.
Source file SHA-256: `415353484b021d45b0a0d02fe3d57049ec1c92dc8ca8da27477e403b0d1f0604`.
Registered source `external-lean-reuse-snapshots-2026-10-21`, fingerprint
`26e8c647ade044fe9bd4dd1f9d997d4ca12aaa4766e55ab31cb64ca9f8415e01`.

Modifications are the `Langlands.NYLL` namespace prefix, extraction of this
single definition, the focused import list, omission of unused opens, and the
direct Mathlib proof of the structure law described above. The subgroup field
and mathematical interface are unchanged. The original copyright and author
header and Apache-2.0 notice are retained; the Library carries
`licenses/NYLL/LICENSE` and `licenses/NYLL/NOTICE`.

Both dependency modules (the concrete subgroup M225.001 and the abstract
filtration M120.001) are independently accepted and published in the Library.
This unit imports them directly and contains no copy or modification of
either dependency pair. In the source the structure law is the term
`fun h => higherPrincipalUnitGroup.antitone F h`, and that theorem's own proof
(`PrincipalUnits/Filtration.lean:97–100` at the pinned commit) is the same
`Ideal.pow_le_pow_right` argument used here, so the definition's data are
unchanged.
