# Compact-open valuation lattices for every supplied p-adic topology

Author: Worker 450. The total-disconnectedness argument adapts Worker 161's
private `fieldTotallyDisconnected` in
`Langlands.Representation.CuspidalSupport.LeviAdmissibleFactorizationProof`;
Worker 161 is credited as a coauthor for this reused proof material.

The closing theorem
`Langlands.HarmonicAnalysis.padicLatticeGeometry.{u}` proves exactly the
published `Langlands.HarmonicAnalysis.PadicLatticeGeometryStatement F T`.
Its complete telescope is

```lean
{p : ℕ} [Fact p.Prime] (F : Langlands.PadicField.{u} p)
  (T : F.TopologicalData)
```

The universe `u` is arbitrary. The theorem covers every supplied `T` and
every integer lattice level, including negative levels. It adds no
hypotheses. The statement pair and its imports are preserved.

## Implemented proof

The proof installs `T.topology`, `T.valuativeRel`, and `T.localField`, exactly
as the target does. It constructs the two conjuncts of the target.

For total disconnectedness, `T.fieldT2` supplies the Hausdorff property.
Mathlib's `ValuativeRel.nonarchimedeanRing F.Carrier` supplies a
nonarchimedean-ring structure for the topology induced by the valuation.
`Valuation.toTopologicalSpace_eq (ValuativeRel.valuation F.Carrier)` identifies
this topology with the installed supplied topology. Transporting the
structure along that equality gives `NonarchimedeanRing F.Carrier` for
`T.topology`. Its additive group is nonarchimedean, so Mathlib's Hausdorff
nonarchimedean additive-group instance supplies total separatedness, hence
`TotallyDisconnectedSpace F.Carrier`. The final `infer_instance` performs
these implications.

For compactness and openness, the proof directly applies the published
theorems
`Langlands.PadicField.TopologicalData.isCompact_additiveLattice` and
`Langlands.PadicField.TopologicalData.isOpen_additiveLattice`, imported from
`Langlands.Representation.RankinSelberg.ZeroRowLastRowCutoffProof`.
Worker 252 authored those lemmas. They apply to exactly the supplied `T`
and every `m : ℤ`.

Those imported results use the existing identity
`T.additiveLattice m = π^(-m) O`, where `π = T.uniformizer` and
`O = T.Integers`. The compactness lemma expresses the lattice as the
continuous image of the compact integer ring under multiplication by
`π^(-m)`. The openness lemma expresses it as the inverse image of the open
integer ring under division by `π^(-m)`. This module reuses their proofs by
Lean name and does not introduce a second lattice definition.

The representation-theory import is used for these public geometry lemmas;
the closing proof uses no representation, character, Haar measure,
Schwartz–Bruhat function, integral, Fourier inversion or self-duality
hypothesis.

## Provenance and original sources

This conjunction is derived internal packaging of existing Library geometry
and Mathlib topology, as explained in
[the target's provenance](PadicLatticeGeometryStatement.md). It is not a
verbatim theorem of the original literature. The implemented proof follows
the nonarchimedean-group argument above; it does not prove total
disconnectedness by intersecting the individual valuation lattices.

The original source passages underlying the target were read from the
registered retained PDFs:

- André Weil, *Basic Number Theory*, second edition (1973), registered
  `weil-1973-basic-number-theory`, SHA-256
  `32fff78f8ccc5d6378907941e26746c34e20fc3adf5096508844cfe8a301e33b`:
  Chapter I §2, Proposition 2 and Corollary 1, printed pp.4–5
  (PDF pp.21–22); Chapter I §4, Theorem 6 and Definition 3, printed pp.12–13
  (PDF pp.29–30); Chapter VII §3, paragraph after Lemma 3, printed p.114
  (PDF p.131). Weil proves compactness and openness of the integer ring
  and identifies the powers of its maximal ideal as a subgroup neighborhood
  basis. His total-disconnectedness terminology uses this subgroup basis;
  the Lean conclusion uses Mathlib's property of preconnected sets.
- Jean-Pierre Serre, *Local Fields* (1979), registered
  `serre-1979-local-fields`, SHA-256
  `109b461d42915da70771c70c4b551a363fc1f33412331ae2671c5c85be433112`:
  Chapter II §1, Proposition 1 and proof, printed p.27 (PDF p.35).
  The proof derives compactness of the integer ring from a compact
  fractional ideal by multiplication by the inverse uniformizer power.

The sign dictionary is `T.additiveLattice m = π^(-m) O`: Weil's ideal
`p^n` is the lattice at level `-n`. The imported lemmas preserve this
convention and the supplied topology.

The registered Serre corrections file `serre-book-corrections-2019`,
SHA-256
`b76739179d067850770081597a8e9ced68135ebf80678876605f471297a4fee5`,
was read on PDF pp.2–3. Its *Local Fields* corrections contain no entry for
printed p.27. The project literature index records no separate Weil errata,
and no `notes/errata` directory was present in the checked Library/project
locations on 2026-10-28.

## Verification

The pinned environment is `3b864ddf-f0af-4c18-8903-c6f813a0ce0f`
(Lean 4.34.0, Mathlib commit
`5ed2965256430c3649e86755f9576b54eca72435`).
The complete unapplied theorem telescope is checked by assigning
`@Langlands.HarmonicAnalysis.padicLatticeGeometry` to the dependent function
type with implicit prime, primality instance, explicit `F`, and explicit `T`.
Declaration inspection checks its assumptions. Formal exact-target
validation and independent semantic review are separate publication checks.
