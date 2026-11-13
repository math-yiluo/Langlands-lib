# Target: the pulled-back valuation-ring map is local

Adapted by Worker 172 from Naganori Yamaguchi, ClassFieldTheory, pinned commit
`fbd320cd8b1b06487c58227e92eb135794267709`, source
`Nyll/ClassFieldTheory/LocalClassFieldTheory/Finite/LocalReciprocity/ResidueAlgebraicallyClosed.lean`
(SHA-256 `86ae7eb949f70864a49e775bc93f8ab6bf45a6e72b75939ad830ded678d0b26b`).
Registered source: `external-lean-reuse-snapshots-2026-10-21`, fingerprint
`26e8c647ade044fe9bd4dd1f9d997d4ca12aaa4766e55ab31cb64ca9f8415e01`. The source file is readable under
`/home/taskhub/pilot/literature/External Lean project reuse survey- pinned source snapshots, 21 October 2026/n-yamaguchi-0729--ClassFieldTheory/source`.

| Unit | Original declaration and source lines | Library declaration |
| --- | --- | --- |
| M237.003 | `valuationSubringComapMap_isLocalHom` (statement 96–97, section binders line 83; proof 98–128) | `Langlands.NYLL.LocalClassFieldTheory.valuationSubringComapMap_isLocalHomStatement` (new target, this file) |
| M237.001 | `valuationSubring_residueField_isAlgClosed` (statement 35–37, binders line 29; proof 38–77) | `Langlands.LocalGalois.residue_isAlgClosed` (already published, reused; no new declaration) |

Original names are in `LocalClassFieldTheory`. The definition
`valuationSubringComapMap` (M237.002) used by M237.003 is in the sibling
`Initial/Definitions.lean`.

## Meaning of the M237.003 target

`valuationSubringComapMap_isLocalHomStatement A` has the binders
`{F Omega : Type u} [Field F] [Field Omega] [Algebra F Omega]` and an explicit
`A : ValuationSubring Omega`. It is the proposition
`IsLocalHom (valuationSubringComapMap (F := F) A)`. That is, the inclusion of the
pulled-back valuation subring `A.comap (algebraMap F Omega)` into `A` reflects
units: an element whose image is a unit of `A` is a unit of the pullback. The
field `F` is implicit. It is determined by the expected type or supplied as
`(F := F)`, as in the source. All four implicit and instance binders occur in the
proposition through `valuationSubringComapMap`, so they survive elaboration. A
`#check` of the elaborated declaration shows exactly
`{F Omega : Type u_1} → [Field F] → [Field Omega] → [Algebra F Omega] → ValuationSubring Omega → Prop`
(private diagnostic `6fdc8789-b55d-4669-932e-c43cac1b8c4c`). The file asserts no proof.

## M237.001 is reused, not duplicated

The source theorem M237.001 has the binders `{Omega : Type u} [Field Omega]
[IsAlgClosed Omega]` and `(A : ValuationSubring Omega)`, and conclusion
`IsAlgClosed (IsLocalRing.ResidueField A)`. The Library already publishes
`Langlands.LocalGalois.residue_isAlgClosed` in `Langlands/Galois/Local/SpectralProof.lean`
(module `Langlands.Galois.Local.SpectralProof`) with the type

```
∀ {L : Type u_1} [inst : Field L] [IsAlgClosed L] (A : ValuationSubring L),
  IsAlgClosed (IsLocalRing.ResidueField ↥A)
```

This is the source statement up to renaming the bound variable. A focused check
compiled, with no errors or warnings, the following term, and the same term with
`Langlands.LocalGalois.residue_isAlgClosed A` against the binder-by-binder source
signature (private diagnostic `6fdc8789-b55d-4669-932e-c43cac1b8c4c`):

```lean
example : (∀ {Omega : Type u} [Field Omega] [IsAlgClosed Omega]
    (A : ValuationSubring Omega), IsAlgClosed (IsLocalRing.ResidueField A)) :=
  @Langlands.LocalGalois.residue_isAlgClosed.{u}
```

So, following the task's reuse constraint, no `Langlands.NYLL` target or proof is
published for M237.001. Consumers of the source name
`valuationSubring_residueField_isAlgClosed` (for example the M249 instance
`localSelectedResidueIsAlgClosed`) use `Langlands.LocalGalois.residue_isAlgClosed A`
by name.

## Modifications

- The source namespace `LocalClassFieldTheory` is prefixed by `Langlands.NYLL`.
- The source theorem M237.003 is replaced by a Prop-valued `def` named with the
  suffix `Statement`. Its explicit argument is the source's
  `(A : ValuationSubring Omega)`, and its body is the source proposition unchanged.
  The implicit and instance binders come from the source's section
  `PurelyInseparableComap` variable line, which is retained. The source proof is
  omitted.
- M237.001 and the source's file-level variable line (line 29, used only by
  M237.001) are omitted, because the Library theorem above covers M237.001.
- The `universe u` declaration and the enclosing `noncomputable section` are retained.
- The four source imports are replaced by the sibling initial definition module.
  No other NYLL declaration is used.

The original copyright and author header is retained. Apache-2.0 attribution
and notices are in `licenses/NYLL/LICENSE` and `licenses/NYLL/NOTICE`.
This support unit makes no claim to discharge the host class-formation, cup,
transfer, Tate or reciprocity targets.
