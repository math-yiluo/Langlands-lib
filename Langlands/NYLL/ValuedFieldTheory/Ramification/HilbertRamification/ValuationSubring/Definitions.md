# Valuation-subring decomposition, inertia and fixed-field aliases

Worker 215 adapts NYLL commands M239.001–003 and M239.011. These are data
abbreviations, with no finiteness, algebraicity or Galois hypothesis.

The pinned original is Naganori Yamaguchi,
`n-yamaguchi-0729/ClassFieldTheory`, commit
`fbd320cd8b1b06487c58227e92eb135794267709`, file
`Nyll/ValuedFieldTheory/Ramification/HilbertRamification/ValuationSubring.lean`.
It is retained under
`/home/taskhub/pilot/literature/External Lean project reuse survey- pinned source snapshots, 21 October 2026/n-yamaguchi-0729--ClassFieldTheory/source`.
The readable source collection is registered as
`nyll-classfieldtheory-fbd320cd-supplement`, fingerprint
`a81005c3aceabc51e9193cdc643d4dd81dd9d496dca2a0cf0111ce610d5b0330`;
the original snapshot registration is
`external-lean-reuse-snapshots-2026-10-21`, fingerprint
`26e8c647ade044fe9bd4dd1f9d997d4ca12aaa4766e55ab31cb64ca9f8415e01`.
The full source file was read, and no NYLL-specific erratum was found in the
Library's `notes/errata/` filenames.

All names below are in
`Langlands.NYLL.RamificationTheory.HilbertRamification.ValuationSubring`.
The source telescope is `(K : Type u) {L : Type v} [Field K] [Field L]
[Algebra K L]`, followed by `(A : _root_.ValuationSubring L)`.
The universes `u` and `v` are independent.

| Command | Original lines | Adapted abbreviation and meaning |
| --- | --- | --- |
| M239.001 | 34–38 (declaration 36) | `decompositionGroup K A : Subgroup (L ≃ₐ[K] L)` is `A.decompositionSubgroup K`, the stabilizer of `A`. |
| M239.002 | 40–44 (declaration 42) | `inertiaGroup K A : Subgroup (decompositionGroup K A)` is `A.inertiaSubgroup K`, the kernel of the residue action. |
| M239.003 | 46–51 (declaration 47) | `residueAction K A` is the monoid homomorphism from the decomposition group to ring automorphisms of `IsLocalRing.ResidueField A`, supplied by `MulSemiringAction.toRingAut`. |
| M239.011 | 152–156 (declaration 154) | `decompositionField K A : IntermediateField K L` is `IntermediateField.fixedField (decompositionGroup K A)`. |

The canonical Mathlib definitions and their existing actions and ring, local-ring
and field structures are reused by Lean name. The wrappers are retained because
downstream NYLL source commands use these names. They introduce no new instance.
In particular the fixed-field definition applies to infinite extensions as well.
The residue action here has ring automorphisms as target; no assertion of
surjectivity or base-residue-field linearity is made by these aliases.

The complete modifications are extraction of these four commands from the larger
source module, prefixing the namespace by `Langlands.NYLL`, and retaining only
`Mathlib.FieldTheory.Galois.Basic` and
`Mathlib.RingTheory.Valuation.RamificationGroup` as imports. Declaration names,
`abbrev` forms, bodies and binders are unchanged. Unrelated ramification groups,
quotients and source proofs are omitted. The original copyright and author header
is preserved; the Apache-2.0 license and third-party notices are retained at
`licenses/NYLL/LICENSE` and `licenses/NYLL/NOTICE`.

Compile in environment `5c94c648-e8dc-4002-a50a-071ebf3f6096` (Lean 4.34.0,
Mathlib `5ed2965256430c3649e86755f9576b54eca72435`). Compilation establishes
elaboration only; independent semantic review and integration establish publication.
