# All-field port of `Langlands.Representation.Whittaker.MirabolicPairingRigidityStep`

`Langlands.AllField.Representation.Whittaker.MirabolicPairingRigidityStep` is the all-field port of the Library module `Langlands.Representation.Whittaker.MirabolicPairingRigidityStep`, which belongs to the Library's development over p-adic fields `F : PadicField p` (with bundled topological data `F.TopologicalData` where a topology is needed). In the port, `F` is an arbitrary field with bundled data `T : LocalFieldData F` (a topology, a valuative relation and an `IsNonarchimedeanLocalField` structure, see `Langlands.LocalFieldData`). Nothing about the characteristic of `F` is assumed, so the port covers every nonarchimedean local field, including those of positive characteristic.

The port imports the original module, so the field-independent declarations of the original are available to it unchanged. It re-declares, under the same name with `Langlands.` replaced by `Langlands.AllField.`, the declarations that involve the field and that the unequal-rank JPSS functional equation needs. Each re-declared declaration keeps the statement, and for a theorem the proof, of its original. Only the field binders change, and the `T`-API (residue cardinality, normalized absolute value, uniformizer and their lemmas) comes from `Langlands.LocalFieldData` and `Langlands.AllField.LocalField.Foundation`.

Source: the original module `Langlands.Representation.Whittaker.MirabolicPairingRigidityStep` in the Library. Its Markdown file gives the literature provenance of each statement.

## Contents

The module docstring of the port:

**The induction step of mirabolic twisted pairing rigidity**

The radical-generated case of `MirabolicTwistedPairingRigidityStatement` in rank
`m + 2` is reduced to rank `m + 1` through the unnormalized Bernstein–Zelevinsky
functor `Φ⁻` of the Library. The reduction uses two statements about `Φ⁻`
(`PhiMinusIrreducibleStatement` and `PhiMinusPairingTransferStatement`) and the
functional multiplicity statement in ranks `m + 1` and `m + 2`.

## Imports from the port

- `Langlands.AllField.Representation.Derivative.MirabolicMinusIrreducibleStatement`
- `Langlands.AllField.Representation.Derivative.MirabolicMinusPairingTransferStatement`
- `Langlands.AllField.Representation.Smooth.SmallRealizationProof`
- `Langlands.AllField.Representation.Whittaker.MirabolicPairingStatement`

## Declarations

- `Langlands.AllField.Whittaker.MirabolicRigidity.exists_functional_ne_zero_of_phiMinus` (theorem): A nonzero Whittaker functional on `Φ⁻ ξ` gives a nonzero Whittaker functional on `ξ`.
- `Langlands.AllField.Whittaker.MirabolicRigidity.nonempty_equiv_of_phiMinus` (theorem): If `Φ⁻ ξ` is irreducible and equivalent to the compact model in rank `m + 1`,
  then `ξ` is equivalent to the compact model in rank `m + 2`.

Public declarations of the original that are not re-declared here: `Langlands.Whittaker.MirabolicRigidity.spectralPoint_sub_one`, `Langlands.Whittaker.MirabolicRigidity.eq_zero_of_bot_eq_top`, `Langlands.Whittaker.MirabolicRigidity.forms_eq_zero_of_bot_eq_top_left`, `Langlands.Whittaker.MirabolicRigidity.forms_eq_zero_of_bot_eq_top_right`, `Langlands.Whittaker.MirabolicRigidity.isIrreducible_of_dichotomy`, `Langlands.Whittaker.MirabolicRigidity.nonempty_linearEquiv_of_multiples`, `Langlands.Whittaker.MirabolicRigidity.upperUnipotent_mem_plusSubgroup`, `Langlands.Whittaker.MirabolicRigidity.plusProjection_mem_upperUnipotent`, `Langlands.Whittaker.MirabolicRigidity.upperUnipotentBlock`, `Langlands.Whittaker.MirabolicRigidity.upperUnipotent_eq_radicalElement_mul_successor`, `Langlands.Whittaker.MirabolicRigidity.mirabolicCharacter_succ`, `Langlands.Whittaker.MirabolicRigidity.radicalGeneratedPairingRigidity_succ`, `Langlands.Whittaker.MirabolicRigidity.mirabolicTwistedPairingRigidity_of_phiMinus`. Each of them either does not involve the p-adic field, and is then available from the original module, or is not used by the functional equation.
