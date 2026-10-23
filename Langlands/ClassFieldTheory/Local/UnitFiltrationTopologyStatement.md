# Topology and compact lifting for actual unit filtrations

Worker 92 authored this statement module. It defines propositions only; no
compactness, separation, lifting, or norm theorem is proved here. All declarations
are in `Langlands.LocalClassField`. The Library proofs are in
[UnitFiltrationStructuralProof](UnitFiltrationStructuralProof.md),
[UnitFiltrationTopologyProof](UnitFiltrationTopologyProof.md), and, for the
separate arithmetic application, [UnitNormProof](UnitNormProof.md).
Worker 159 corrected the documentation of their availability.

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
extra field assumptions in this criterion. The published
`unitFiltrationStructuralLaws` proves them from the actual local-field data;
`unitFiltrationCompactLifting` uses that result to prove the criterion with
exactly the preservation and one-level approximation hypotheses above.

`UnitFiltrationTopologyTheorems.{u,v}` is the complete target: structural laws
in universe `u`, structural laws in universe `v`, and the lifting criterion
between those universes. The published
`unitFiltrationTopologyTheorems.{u,v}` proves this exact conjunction, including
both structural-law instances.

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
the published structural proof establishes separation using Krull intersection
for the maximal-ideal powers in the Noetherian local integer ring. These are
derived assertions, not a claim that Serre states the exact Lean bundle or this
implemented proof route verbatim.

The lifting criterion is a derived compact local-field specialization of the
surjectivity part of Lemma 2, with the filtration shifted by any starting level
`n`. Preservation makes the maps on successive quotients well defined, and the
stated one-level approximation expresses their surjectivity without introducing
quotient representatives as additional data. The published topology proof
constructs successive corrections and then nested nonempty closed sets of
approximate preimages in the compact source level. Compactness supplies a common
preimage candidate, and target separation forces its error to be `1`.
`unitFiltrationCompactLifting_of_structural` isolates the argument with structural
laws as premises; `unitFiltrationCompactLifting` discharges those premises using
the published structural theorem. The implementation is in the separate proof
module; this statement module still contains only proposition definitions.

This is a conditional auxiliary theorem for arbitrary continuous homomorphisms.
The separate published `unramifiedUnitNorms.{u,v}` in `UnitNormProof` proves
`UnramifiedUnitNorms.{u,v}` for the actual determinant norm of a compatible finite
extension, with arbitrary supplied topological data and equality of the absolute
ramification indices. It establishes continuity, preservation and one-level
approximation for that norm and applies compact lifting. Thus its final statement
has no additional preservation or approximation premises, requires no Galois
hypothesis, and covers every level including zero in two independent carrier
universes. This proves the unramified-unit-norm target, not the entire
`UnitNormTheorems` bundle or local reciprocity. The statement module imports none
of these proof modules.

## Dependency and duplicate audit

The module imports the existing `Langlands.ClassFieldTheory.Local.Units` and Mathlib's
`Topology.Compactness.Compact`. The units
module supplies the exact subgroups and reductions but no structural-law or
compact-lifting theorem. `UnitFiltrationStructuralProof` proves the structural
laws, and `UnitFiltrationTopologyProof` imports that proof and proves the compact
lifting criterion and complete topology bundle. The existing `UnitNormStatement`
states the arithmetic norm conclusion used by `UnitNormProof`.

The topology proof uses Mathlib's general compact-intersection tool
`IsCompact.nonempty_iInter_of_sequence_nonempty_isCompact_isClosed` in
`Mathlib/Topology/Compactness/Compact.lean`. The structural proof also imports
the existing local-field topology and Mathlib's Krull intersection theorem.
These separate proof modules supply the results for the actual filtration;
the general Mathlib tools alone do not state this bundle. The published
`Langlands.LocalField.Normalization.Proof` supplies arithmetic comparisons used
by the norm application and is not needed for this statement.

The pinned environment is Lean 4.34.0 with Mathlib commit
`5ed2965256430c3649e86755f9576b54eca72435`.
