# All-field port of `Langlands.Representation.Whittaker.MirabolicFiniteLengthDetection`

`Langlands.AllField.Representation.Whittaker.MirabolicFiniteLengthDetection` is the all-field port of the Library module `Langlands.Representation.Whittaker.MirabolicFiniteLengthDetection`, which belongs to the Library's development over p-adic fields `F : PadicField p` (with bundled topological data `F.TopologicalData` where a topology is needed). In the port, `F` is an arbitrary field with bundled data `T : LocalFieldData F` (a topology, a valuative relation and an `IsNonarchimedeanLocalField` structure, see `Langlands.LocalFieldData`). Nothing about the characteristic of `F` is assumed, so the port covers every nonarchimedean local field, including those of positive characteristic.

The port imports the original module, so the field-independent declarations of the original are available to it unchanged. It re-declares, under the same name with `Langlands.` replaced by `Langlands.AllField.`, the declarations that involve the field and that the unequal-rank JPSS functional equation needs. Each re-declared declaration keeps the statement, and for a theorem the proof, of its original. Only the field binders change, and the `T`-API (residue cardinality, normalized absolute value, uniformizer and their lemmas) comes from `Langlands.LocalFieldData` and `Langlands.AllField.LocalField.Foundation`.

Source: the original module `Langlands.Representation.Whittaker.MirabolicFiniteLengthDetection` in the Library. Its Markdown file gives the literature provenance of each statement.

## Contents

The module docstring of the port:

**Detection of nonzero mirabolic representations by twisted coinvariants**

A smooth representation of the actual mirabolic group is zero as soon as its
coinvariants vanish for all the characters `θ_S` of the upper-unipotent group,
`θ_S(u) = ψ(∑_{i ∈ S} u_{i,i+1})`, `S` a set of simple roots. The radical step
uses a nonzero vector, a maximal ideal of the group algebra of the radical and
the classification of its locally constant characters.

## Imports from the port

- `Langlands.AllField.Representation.Derivative.MirabolicCharacter`
- `Langlands.AllField.Representation.Whittaker.MirabolicFiniteLengthCharacters`

## Declarations

- `Langlands.AllField.Whittaker.MirabolicFiniteLength.isLimitOfCompactSubgroups_pi` (theorem): The vector group `F^m` is exhausted by the compact open lattices `L_k^m`.
- `Langlands.AllField.Whittaker.MirabolicFiniteLength.exists_relations_ne_top` (theorem): A nonzero smooth representation of the actual mirabolic group `P_(n+1)` has
  nonzero coinvariants for some simple character `θ_S` of its upper-unipotent
  subgroup. Here `ψ` generates the locally constant characters of `F`.

Public declarations of the original that are not re-declared here: `Langlands.Whittaker.MirabolicFiniteLength.isInvariant_bot`, `Langlands.Whittaker.MirabolicFiniteLength.relations_eq_of_surjective`, `Langlands.Whittaker.MirabolicFiniteLength.apply_mem_relations`, `Langlands.Whittaker.MirabolicFiniteLength.relations_eq_bot_of_subsingleton`, `Langlands.Whittaker.MirabolicFiniteLength.mem_relations_of_injective`, `Langlands.Whittaker.MirabolicFiniteLength.isLimitOfCompactSubgroups_top`, `Langlands.Whittaker.MirabolicFiniteLength.exists_pow_mem_of_isOpen`, `Langlands.Whittaker.MirabolicFiniteLength.exists_character_not_mem_relations`, `Langlands.Whittaker.MirabolicFiniteLength.selectedSum`, `Langlands.Whittaker.MirabolicFiniteLength.simpleCharacter`, `Langlands.Whittaker.MirabolicFiniteLength.simpleCharacter_apply`, `Langlands.Whittaker.MirabolicFiniteLength.radicalCharacter`, `Langlands.Whittaker.MirabolicFiniteLength.radicalCharacter_apply`, `Langlands.Whittaker.MirabolicFiniteLength.radicalCharacter_isInvariant`, `Langlands.Whittaker.MirabolicFiniteLength.topLeftMatrix`, `Langlands.Whittaker.MirabolicFiniteLength.topLeftMatrix_isUpperTriangular`, `Langlands.Whittaker.MirabolicFiniteLength.topLeftMatrix_diag`, `Langlands.Whittaker.MirabolicFiniteLength.det_topLeftMatrix`, `Langlands.Whittaker.MirabolicFiniteLength.topLeftGL`, `Langlands.Whittaker.MirabolicFiniteLength.topLeftGL_mem_upperUnipotent`, `Langlands.Whittaker.MirabolicFiniteLength.topLeft`, `Langlands.Whittaker.MirabolicFiniteLength.topLeft_apply`, `Langlands.Whittaker.MirabolicFiniteLength.successor_bottom`, `Langlands.Whittaker.MirabolicFiniteLength.lastColumn`, `Langlands.Whittaker.MirabolicFiniteLength.eq_radicalElement_mul_successor`, `Langlands.Whittaker.MirabolicFiniteLength.simpleCharacter_snoc`, `Langlands.Whittaker.MirabolicFiniteLength.radicalQuotient`, `Langlands.Whittaker.MirabolicFiniteLength.radicalQuotient_mk`, `Langlands.Whittaker.MirabolicFiniteLength.mk_mem_relations`. Each of them either does not involve the p-adic field, and is then available from the original module, or is not used by the functional equation.
