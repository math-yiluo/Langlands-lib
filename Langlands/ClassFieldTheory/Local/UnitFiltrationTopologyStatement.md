# Topology and compact lifting for actual unit filtrations

Worker 92 authored this statement module. It defines propositions only; no
compactness, separation, lifting, or norm theorem is proved here. All declarations
are in `Langlands.LocalClassField`.

## Exact statements

`UnitFiltrationStructuralLaws.{u}` quantifies every prime `p`, every
`F : PadicField.{u} p`, and every supplied `T : F.TopologicalData`. After
installing `T.topology`, `F.Carrierˣ` has Mathlib's induced units topology.
The proposition asserts, in conjunction:

- For every natural `n`, the subset underlying `T.unitFiltration n` is compact
  and closed in `F.Carrierˣ`.
- `T.unitFiltration` is antitone for the subgroup inclusion order.
- A field unit belonging to every filtration level is `1`. Since every level
  is a subgroup, this is equivalent to their intersection being the trivial
  subgroup.
- `T.unitFiltration 0 = T.unitSubgroup`.

The subgroups are exactly those of `Langlands.ClassFieldTheory.Local.Units`:
`T.congruenceUnits n` is the kernel of reduction on integer units modulo the
`n`th power of the actual maximal ideal, and `T.unitFiltration n` is its image
under `T.integerUnitsInclusion`. No subgroup is replaced by a valuation bound.
At zero the quotient ring is the zero ring, so the reduction kernel is the
whole integer-unit group; the equality to the valuation-unit subgroup is part
of the target. All assertions include zero.

`UnitFiltrationCompactLifting.{u,v}` quantifies every prime, independent
`F : PadicField.{u} p` and `E : PadicField.{v} p`, and arbitrary supplied
`T` and `S`. The local `T.topology` and `S.topology` instances determine the
units topologies used by the continuous homomorphism
`f : E.Carrierˣ →ₜ* F.Carrierˣ`. There is no algebra structure or extension
relation between `F` and `E` in this proposition. Its only additional
hypotheses are:

- Preservation: for each natural `n`, `f` sends `S.unitFiltration n` into
  `T.unitFiltration n`.
- One-level approximation: for each natural `n` and `y ∈ T.unitFiltration n`,
  there is `x ∈ S.unitFiltration n` such that
  `y * (f x)⁻¹ ∈ T.unitFiltration (n + 1)`.

The conclusion is equality of actual subgroups
`(S.unitFiltration n).map f.toMonoidHom = T.unitFiltration n` for every `n`.
In particular it includes surjectivity onto the full valuation-unit subgroup
at `n = 0`. The topology, compactness, closedness and separation facts are not
extra field assumptions in this criterion. They are obligations for its future
proof using the actual local-field data.

`UnitFiltrationTopologyTheorems.{u,v}` is the complete target: structural laws
in universe `u`, structural laws in universe `v`, and the lifting criterion
between those universes. Including both structural-law instances lets a future
proof of this single target supply the prerequisites for both fields.

## Source correspondence and derived scope

The source is Jean-Pierre Serre, *Local Fields*, English translation by Marvin
Jay Greenberg, GTM 67, Springer, 1979; source ID `serre-1979-local-fields`,
SHA256 `109b461d42915da70771c70c4b551a363fc1f33412331ae2671c5c85be433112`,
retained at `/home/taskhub/central-library/Serre--Local Fields--1979.pdf`.
Worker 92 read the following original passages:

- Chapter II, Section 1, printed pp. 26–28 (PDF pp. 34–36), especially
  Proposition 1 on p. 27: valuation topology and compactness of the integer
  ring for a complete discretely valued field with finite residue field.
- Chapter IV, Section 2, printed p. 66 (PDF p. 73): the convention
  `U^0 = U`, the positive congruence levels, their closedness, decreasing
  order, and the separated filtration topology.
- Chapter V, Section 1, Lemma 2, printed p. 81 (PDF p. 88): surjectivity from
  surjectivity on successive quotients for complete separated filtered
  abelian groups.
- Chapter V, Section 2, Propositions 1–3, printed pp. 81–82 (PDF pp. 88–89):
  the separate arithmetic norm application.

The structural bundle specializes the first two passages to the published
actual p-adic fields. Compactness of all levels follows mathematically from
compactness of the integer ring and closedness of the unit congruence groups;
separation uses the Hausdorff valuation topology. These are derived assertions,
not a claim that Serre states the exact Lean bundle verbatim.

The lifting criterion is a derived compact local-field specialization of the
surjectivity part of Lemma 2, with the filtration shifted by any starting level
`n`. Preservation makes the maps on successive quotients well defined, and the
stated one-level approximation expresses their surjectivity without introducing
quotient representatives as additional data. A possible future proof constructs
nested nonempty closed sets of approximate preimages in the compact source
level. Compactness supplies a common preimage candidate, and target separation
forces its error to be `1`. This describes the intended mathematical reduction;
there is no implemented Lean proof in this module.

This is a conditional auxiliary target for arbitrary continuous homomorphisms.
The unconditional `UnramifiedUnitNorms` target remains a separate arithmetic
obligation: its proof must establish preservation, continuity, and the
one-level approximation for the actual determinant norm. Neither a norm
surjectivity theorem, surjectivity at all finite truncations, nor local
reciprocity is assumed or imported here.

## Dependency and duplicate audit

The module imports the existing `Langlands.ClassFieldTheory.Local.Units` and Mathlib's
`Topology.Compactness.Compact`. It changes no existing Library pair. The units
module supplies the exact subgroups and reductions but no structural-law or
compact-lifting theorem. The existing `UnitNormStatement` states the arithmetic
norm conclusion and does not provide this auxiliary criterion.

A search of the current Library and pinned Mathlib topology and p-adic sources
found no statement for these actual unit filtrations and no duplicate lifting
criterion. Mathlib does provide general compact-intersection tools, including
`IsCompact.inter_iInter_nonempty` and
`IsCompact.nonempty_iInter_of_sequence_nonempty_isCompact_isClosed` in
`Mathlib/Topology/Compactness/Compact.lean`; these are possible ingredients for
the later proof, not proofs of the present statements. The published
`Langlands.LocalField.Normalization.Proof` also supplies arithmetic and topology
comparisons if needed by that proof, but is not needed for this statement.

The pinned environment is Lean 4.34.0 with Mathlib commit
`5ed2965256430c3649e86755f9576b54eca72435`.
