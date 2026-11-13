# All-field port of `Langlands.Representation.Whittaker.ParabolicInducedCoinvariantFinitenessProof`

`Langlands.AllField.Representation.Whittaker.ParabolicInducedCoinvariantFinitenessProof` is the all-field port of the Library module `Langlands.Representation.Whittaker.ParabolicInducedCoinvariantFinitenessProof`, which belongs to the Library's development over p-adic fields `F : PadicField p` (with bundled topological data `F.TopologicalData` where a topology is needed). In the port, `F` is an arbitrary field with bundled data `T : LocalFieldData F` (a topology, a valuative relation and an `IsNonarchimedeanLocalField` structure, see `Langlands.LocalFieldData`). Nothing about the characteristic of `F` is assumed, so the port covers every nonarchimedean local field, including those of positive characteristic.

The port imports the original module, so the field-independent declarations of the original are available to it unchanged. It re-declares, under the same name with `Langlands.` replaced by `Langlands.AllField.`, the declarations that involve the field and that the unequal-rank JPSS functional equation needs. Except for the changes described under Proof route below, each re-declared declaration keeps the statement, and for a theorem the proof, of its original. Only the field binders and the canonical data of the original (see the next paragraph) change, and the `T`-API (residue cardinality, normalized absolute value, uniformizer and their lemmas) comes from `Langlands.LocalFieldData` and `Langlands.AllField.LocalField.Foundation`.

The original uses the canonical topological data `F.canonicalTopologicalData` of the p-adic field, and transports a supplied realization to it (`topology_eq_canonical…`). The port uses the supplied data `T : LocalFieldData F` throughout. Where the original quantifies over a p-adic field with its canonical data, the port quantifies over a field `F` and arbitrary data `T`. The transport is then unnecessary and is omitted.

Source: the original module `Langlands.Representation.Whittaker.ParabolicInducedCoinvariantFinitenessProof` in the Library. Its Markdown file gives the literature provenance of each statement.

## Contents

The module docstring of the port:

**Proof that normalized parabolic induction preserves finite character coinvariants**

The finite upper-unipotent orbit filtration of the normalized induced module,
compact localization on each orbit, and the embedded Levi upper-unipotent group
in each orbit stabilizer reduce the conclusion to the coefficient premise.

## Proof route

In the original, the private theorem `core` proves the target only for the canonical
topology `F.canonicalTopologicalData.topology` and the canonical half modulus
`F.canonicalTopologicalData.parabolicHalfModulus B`. The final theorem
`parabolicInducedCoinvariantFiniteness` reaches a supplied `T` through an auxiliary
statement `key`: it rewrites `T.topology` to the canonical topology
(`topology_eq_canonicalModule`) and `T.parabolicHalfModulus B` to the canonical half
modulus (`parabolicHalfModulus_eq`).

In the port, `core F T m B` is proved directly for `T.topology` and
`T.parabolicHalfModulus B`. The private theorem `stabilizerCoinvariants_finite` that it uses
is likewise stated for `T` instead of the canonical data, and the private definition `Body`
only has its field binder replaced. The final theorem only writes `n = m + 1` and calls
`core F T m B`, so the transport step `key` is gone. The steps inside `core` and
`stabilizerCoinvariants_finite` are those of the original, with two changes. The facts about
the half modulus (`parabolicHalfModulus_section`, `leviHalfModulus_eq_one`,
`normOneLevi_le_ker_leviModulus`, `mem_normOneLevi`, `isOpen_ker_parabolicHalfModulus`) are
taken from `T` instead of `F.canonicalTopologicalData`. The ported inputs
`Parabolic.parabolicQuotientCompact`, `unipotentOrbit` and `compactLocalization` are applied
at `F` and `T`.

## Imports from the port

- `Langlands.AllField.Representation.Parabolic.QuotientCompactProof`
- `Langlands.AllField.Representation.Whittaker.CompactLocalizationProof`
- `Langlands.AllField.Representation.Whittaker.ParabolicInducedCoinvariantFinitenessStatement`
- `Langlands.AllField.Representation.Whittaker.UnipotentOrbitProof`

## Declarations

- `Langlands.AllField.Whittaker.parabolicInducedCoinvariantFiniteness` (theorem): Normalized parabolic induction preserves finite-dimensionality of all locally
  constant upper-unipotent character quotients, given the same for the coefficient.
