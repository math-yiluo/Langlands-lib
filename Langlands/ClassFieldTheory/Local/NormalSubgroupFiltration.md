# Antitone filtrations by normal subgroups

Module `Langlands.ClassFieldTheory.Local.NormalSubgroupFiltration`, namespace
`Langlands.ClassFieldTheory.Local.NormalSubgroupFiltration`. This file belongs to the Library. The
ramification theory of the NYLL library (the copy under `Nyll/`) works with the structure
`RamificationTheory.DiscreteValuationField.AntitoneNormalSubgroupFiltration G` of
`Nyll/ValuedFieldTheory/Ramification/GaloisValuation/RamificationQuotients.lean`: for a group `G`, a
sequence `lower : ℕ → Subgroup G` of normal subgroups (`lower_normal`, with the instance
`lower_normal_instance`) which decreases (`antitone : m ≤ n → lower n ≤ lower m`). The Library uses
this structure for towers of open normal subgroups: `Langlands.CongruenceTower` of the module
`Langlands.Shimura.DefiniteFormsTower` extends it.

This file states the two laws of the structure in Mathlib's vocabulary:

- `antitone_lower F : Antitone F.lower`;
- `normal_lower F n : (F.lower n).Normal`.

## Complete types

As printed by `PrettyPrinter.ppSignature`:

```lean
Langlands.ClassFieldTheory.Local.NormalSubgroupFiltration.antitone_lower.{u} {G : Type u} [Group G]
  (F : RamificationTheory.DiscreteValuationField.AntitoneNormalSubgroupFiltration G) : Antitone F.lower
Langlands.ClassFieldTheory.Local.NormalSubgroupFiltration.normal_lower.{u} {G : Type u} [Group G]
  (F : RamificationTheory.DiscreteValuationField.AntitoneNormalSubgroupFiltration G) (n : ℕ) : (F.lower n).Normal
```

## Proofs

Both are the fields `antitone` and `lower_normal` of the structure.

## Declarations

`antitone_lower`, `normal_lower`.

## Declarations used

From the NYLL copy: `RamificationTheory.DiscreteValuationField.AntitoneNormalSubgroupFiltration`
(fields `lower`, `lower_normal`, `antitone`).

## Sources

No source is cited: the statements are the defining properties of the structure.
