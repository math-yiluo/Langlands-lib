# The ring map from a pulled-back valuation subring

Adapted by Worker 172 from Naganori Yamaguchi, ClassFieldTheory, pinned commit
`fbd320cd8b1b06487c58227e92eb135794267709`, source
`Nyll/ClassFieldTheory/LocalClassFieldTheory/Finite/LocalReciprocity/ResidueAlgebraicallyClosed.lean`
(SHA-256 `86ae7eb949f70864a49e775bc93f8ab6bf45a6e72b75939ad830ded678d0b26b`).
Registered source: `external-lean-reuse-snapshots-2026-10-21`, fingerprint
`26e8c647ade044fe9bd4dd1f9d997d4ca12aaa4766e55ab31cb64ca9f8415e01`. The source file is readable under
`/home/taskhub/pilot/literature/External Lean project reuse survey- pinned source snapshots, 21 October 2026/n-yamaguchi-0729--ClassFieldTheory/source`.

| Unit | Original declaration and source lines | Adapted declaration |
| --- | --- | --- |
| M237.002 | `valuationSubringComapMap` (85–93, in section `PurelyInseparableComap`, lines 81–83) | `valuationSubringComapMap` |

The original name is in `LocalClassFieldTheory`; the adapted name is in
`Langlands.NYLL.LocalClassFieldTheory`.

## Meaning

For fields `F Omega : Type u` with an algebra structure `[Algebra F Omega]` and a
valuation subring `A` of `Omega`, `A.comap (algebraMap F Omega)` is the valuation
subring of `F` of elements whose image lies in `A`. The definition is the ring
homomorphism from this pulled-back subring to `A` sending `x` to
`algebraMap F Omega x`, packaged with its membership proof `x.property`. The
ring-homomorphism axioms are discharged by the corresponding facts for
`algebraMap F Omega` through `Subtype.ext`.

## Modifications

- The source namespace `LocalClassFieldTheory` is prefixed by `Langlands.NYLL`.
- Only this definition is extracted. Its section `PurelyInseparableComap`, the
  binders `{F Omega : Type u} [Field F] [Field Omega] [Algebra F Omega]`, the
  `universe u` declaration (source line 27), the enclosing `noncomputable section`
  (source line 25), the docstring and the definition body are retained unchanged.
- The four source imports (one NYLL module and three Mathlib modules) are
  replaced by the single Mathlib module `Mathlib.RingTheory.Valuation.ValuationSubring`,
  which suffices for this definition. No NYLL declaration is used.
- The source's file-level variable line (line 29, used only by M237.001) and all
  theorems are omitted here. The sibling `Initial/Statements.lean` states M237.003. M237.001 is already supplied by the existing `Langlands.LocalGalois.residue_isAlgClosed`, as explained in that sibling's Markdown.

The original copyright and author header is retained. Apache-2.0 attribution
and notices are in `licenses/NYLL/LICENSE` and `licenses/NYLL/NOTICE`.
This support unit makes no claim to discharge the host class-formation, cup,
transfer, Tate or reciprocity targets.
