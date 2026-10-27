# Compact-open valuation lattices for a supplied p-adic topology

`Langlands.HarmonicAnalysis.PadicLatticeGeometryStatement.{u}` is a Prop-valued
definition. It states that every supplied topology on a finite extension of
`ℚ_p` is totally disconnected and that every actual valuation lattice
`T.additiveLattice m` is compact and open in it. The module supplies no proof.
The proposition is a derived internal prerequisite, not a verbatim theorem of
the cited sources.

## Exact telescope

The declaration has the parameters

```text
{p : ℕ} [Fact p.Prime] (F : Langlands.PadicField.{u} p) (T : F.TopologicalData)
```

in this order: the prime and its primality instance are implicit, while the
field and its topological data are explicit. The field universe `u` is
arbitrary, and the proposition is stated for every supplied `T`, not for a
chosen or canonical topology. The type of the declaration is

```text
{p : ℕ} → [Fact p.Prime] → (F : Langlands.PadicField.{u} p) → F.TopologicalData → Prop.
```

## The proposition

The body installs the three supplied instances `letI := T.topology`,
`letI := T.valuativeRel` and `letI := T.localField`, and then states

```text
TotallyDisconnectedSpace F.Carrier ∧
  ∀ m : ℤ, IsCompact (T.additiveLattice m : Set F.Carrier) ∧
    IsOpen (T.additiveLattice m : Set F.Carrier).
```

- The first conjunct is Mathlib's `TotallyDisconnectedSpace` class for the
  topology `T.topology`. It is a proposition: every preconnected subset of
  `F.Carrier` has at most one point. It is a conclusion, so a consumer can
  take it as the certificate `htd` required by the existential
  `∃ htd : TotallyDisconnectedSpace F.Carrier` in
  `Langlands.HarmonicAnalysis.PadicSelfDualMeasureExistsStatement`. That
  statement installs the same three instances.
- The second conjunct holds for every integer `m`, including negative `m`,
  with no restriction. For each `m` it asserts both `IsCompact` and `IsOpen`
  of the same set, the coercion to `Set F.Carrier` of the additive subgroup
  `T.additiveLattice m`.

All three facts concern only the topology `T.topology`. The instances
`T.valuativeRel` and `T.localField` are installed as the task requires, and no
term of the conclusion depends on them. `IsNonarchimedeanLocalField` takes a
topology as a parameter and provides none, so `T.topology` is the only topology
in scope. No hypothesis is added. In particular, the proposition contains no
Fourier inversion, no self-dual measure, no other choice of topology, and no
assumed compactness or openness. No Haar measure, additive character,
Schwartz–Bruhat function or integral appears, because none is needed for these
three facts.

## The lattices

`T.additiveLattice m` is the existing Library definition in
`Langlands.HarmonicAnalysis.Conductor`, reused unchanged:

```text
T.additiveLattice m = {x | T.discreteValuation x ≤ WithZero.exp m}.
```

The valuation `T.discreteValuation` is the normalized `ℤᵐ⁰`-valued valuation
of the supplied data. Its chosen uniformizer `T.uniformizer` has valuation
`WithZero.exp (-1)`. The published lemmas in
`Langlands.PadicField.TopologicalData` give the following conventions.

- `mem_additiveLattice_iff_div_mem_integers`: `x ∈ T.additiveLattice m` exactly
  when `x / T.uniformizer ^ (-m) ∈ T.Integers`. So the lattice is the
  fractional ideal `π^(-m) O`, with `O = T.Integers`.
- `additiveLattice_mono`: the lattices increase with `m`.
- `mem_additiveLattice_zero`: level zero is exactly the existing integer ring
  `T.Integers`.

`T.Integers` is the existing integer ring and is not redefined.
`Langlands.HarmonicAnalysis.PadicScalarHaarScalingProof` already proves
`Langlands.PadicField.TopologicalData.isCompact_integers` and
`Langlands.PadicField.TopologicalData.isOpen_integers` for every supplied `T`.
With `mem_additiveLattice_zero` these give the case `m = 0` of the second
conjunct. The proposition adds the cases `m ≠ 0` and total disconnectedness.

## Original sources and derivation

- André Weil, *Basic Number Theory*, second edition, Grundlehren 144,
  Springer, 1973. Registered source `weil-1973-basic-number-theory`; retained
  file
  `/home/taskhub/central-library/Weil--Basic number theory (book, 2nd edition)--1973.pdf`;
  SHA-256
  `32fff78f8ccc5d6378907941e26746c34e20fc3adf5096508844cfe8a301e33b`
  (verified on 2026-10-27).
  - Chapter I §2, Proposition 2 and its Corollary 1, printed pp. 4–5 / PDF
    pp. 21–22. In a non-discrete locally compact field `K`, each set
    `B_m = {x : mod_K(x) ≤ m}` with `m > 0` is compact, and these sets form a
    fundamental system of neighborhoods of `0`.
  - Chapter I §4, Theorem 6 and its proof, printed pp. 12–13 / PDF pp. 29–30.
    For a p-field, `R = {mod_K(x) ≤ 1}` is compact and open, and so is
    `P = πR`. Definition 3 on printed p. 13 / PDF p. 30 sets `p^n = π^n R`.
    This is the set of `x` with `ord(x) ≥ n`.
  - Chapter VII §3, the paragraph after Lemma 3, printed p. 114 / PDF p. 131.
    Weil calls a group totally disconnected if the neutral element has a
    fundamental system of neighborhoods consisting of subgroups. He states
    that for a p-field `K` the group `K` has this property, because the
    `p^n` form such a system.
- Jean-Pierre Serre, *Local Fields*, Graduate Texts in Mathematics 67,
  Springer, 1979, Chapter II §1, printed p. 27 / PDF p. 35, Proposition 1
  and its proof. The ideals `π^n A` form a fundamental system of closed
  neighborhoods of `0`. If `K` is locally compact, one of them is compact,
  and multiplying by `π^(-n)` shows that `A` is compact. Registered source
  `serre-1979-local-fields`; retained file
  `/home/taskhub/central-library/Serre--Local Fields--1979.pdf`; SHA-256
  `109b461d42915da70771c70c4b551a363fc1f33412331ae2671c5c85be433112`
  (verified on 2026-10-27).

The pages above were read from the retained PDFs by text extraction.

**Dictionary.** Each supplied `T` makes `F.Carrier` a commutative p-field in
Weil's sense. The normalized valuation gives the following correspondences.

- Weil's `R`, or Serre's `A`, is `T.Integers`.
- Weil's `p^n = π^n R` is `T.additiveLattice (-n)`.
- `T.additiveLattice m` is `p^(-m)`.

Every lattice in the proposition is therefore one of the sets that Weil and
Serre show to be compact neighborhoods of `0`. A subgroup that is a
neighborhood of `0` is open.

**Total disconnectedness.** Weil's definition of total disconnectedness is a
property of the neighborhoods of the identity. Mathlib's `TotallyDisconnectedSpace`
says instead that every preconnected subset has at most one point. The
proposition uses Mathlib's notion. For the additive group of a supplied p-adic
field, Weil's property implies Mathlib's. Every open subgroup is also closed.
So any preconnected set containing `0` lies in each `T.additiveLattice m`, and
the intersection of all these lattices is `{0}`, because a nonzero `x` lies
outside `T.additiveLattice k` once `WithZero.exp k` is below its valuation.
Translation handles a preconnected set through any other point. The sources
do not state the conjunction as one theorem. The formulation through the
Library's `additiveLattice`, the Mathlib predicates and the explicit
certificate is derived Lean packaging.

**Errata.** The project literature index registers no errata for Weil (1973).
For Serre (1979) it registers the author's corrections file
`serre-book-corrections-2019`: Jean-Pierre Serre, *Corrections to J-P.
Serre's books*, Collège de France author file, 2019; retained file
`/home/taskhub/pilot/literature/Jean-Pierre Serre — Corrections to J-P. Serre's books (2019).pdf`;
SHA-256
`b76739179d067850770081597a8e9ced68135ebf80678876605f471297a4fee5`
(verified on 2026-10-27). Its section on *Local Fields* (Springer-Verlag,
third printing, 1979), PDF pp. 2–3, was read. It lists corrections to printed
pp. 14, 15, 31, 63, 74, 75 and to pages from p. 110 on. It lists none for
printed p. 27, so it does not affect the cited Chapter II §1, Proposition 1.
The Library has no `notes/errata` directory (checked on 2026-10-27).

## Purpose and remaining proof obligation

Worker 688 split this prerequisite from task
`2be3a65c-9439-43c6-be52-368dd3a8bf98` revision 2, which must prove
`Langlands.HarmonicAnalysis.PadicSelfDualMeasureExistsStatement` for every
prime, every `PadicField.{u}` and every supplied `TopologicalData`. The first
conjunct supplies that statement's total-disconnectedness certificate. The
second supplies compact open lattices at every level, as used for test
functions and lattice volumes. This proposition does not change or prove that
statement.

A future proof must establish all three facts from the supplied data alone.
Worker 180 suggested a route for total disconnectedness:

- import `Mathlib.Topology.Algebra.Nonarchimedean.TotallyDisconnected`;
- obtain `NonarchimedeanRing F.Carrier` from `ValuativeRel.nonarchimedeanRing`,
  transported along
  `(ValuativeRel.valuation F.Carrier).toTopologicalSpace_eq`;
- conclude with Mathlib's total-separatedness instance for Hausdorff
  nonarchimedean groups.

For the lattices, one possible route is the following:

- multiplication by `T.uniformizer ^ (-m)` is a homeomorphism that maps
  `T.Integers` onto `T.additiveLattice m`;
- combine this with `isCompact_integers` and `isOpen_integers`.

These routes are suggestions. They are neither implemented nor assumed.
Compilation checks only that the declaration is a well-formed proposition. It
does not establish the mathematical claim.

## Environment and authorship

The environment is `3b864ddf-f0af-4c18-8903-c6f813a0ce0f`, with Lean 4.34.0 and
Mathlib commit `5ed2965256430c3649e86755f9576b54eca72435`. The module imports
only `Langlands.HarmonicAnalysis.Conductor`. Worker 723 authored this pair from
the formulation in task `8031460c-9263-44a4-a117-e80aed4f1458` revision 1.
