# The residue-field map of a pulled-back valuation subring

Adapted by Worker 172 from Naganori Yamaguchi, ClassFieldTheory, pinned commit
`fbd320cd8b1b06487c58227e92eb135794267709`, source
`Nyll/ClassFieldTheory/LocalClassFieldTheory/Finite/LocalReciprocity/ResidueAlgebraicallyClosed.lean`
(SHA-256 `86ae7eb949f70864a49e775bc93f8ab6bf45a6e72b75939ad830ded678d0b26b`).
Registered source: `external-lean-reuse-snapshots-2026-10-21`, fingerprint
`26e8c647ade044fe9bd4dd1f9d997d4ca12aaa4766e55ab31cb64ca9f8415e01`. The source file is readable under
`/home/taskhub/pilot/literature/External Lean project reuse survey- pinned source snapshots, 21 October 2026/n-yamaguchi-0729--ClassFieldTheory/source`.

| Unit | Original declaration and source lines | Adapted declaration |
| --- | --- | --- |
| M237.004 | `valuationSubringComapResidueMap` (130–137, in section `PurelyInseparableComap`, lines 81–83) | `valuationSubringComapResidueMap` |

The original name is in `LocalClassFieldTheory`; the adapted name is in
`Langlands.NYLL.LocalClassFieldTheory`.

## Meaning

For fields `F Omega : Type u` with `[Algebra F Omega]` and a valuation subring
`A` of `Omega`, let `B = A.comap (algebraMap F Omega)` be the pulled-back
valuation subring of `F`. The published definition `valuationSubringComapMap A :
B →+* A` (M237.002) is a local homomorphism by the published theorem
`valuationSubringComapMap_isLocalHom` (M237.003). This definition is the induced
ring homomorphism of residue fields

`IsLocalRing.ResidueField B →+* IsLocalRing.ResidueField A`,

namely Mathlib's `IsLocalRing.ResidueField.map (valuationSubringComapMap A)`,
which sends the residue of `x : B` to the residue of
`valuationSubringComapMap A x`. The `IsLocalHom` instance that
`IsLocalRing.ResidueField.map` requires is supplied by a local `letI` from the
M237.003 theorem. The field `F` is implicit and is determined by the expected
type or supplied as `(F := F)`.

A `#check` of the elaborated declaration shows exactly
`{F Omega : Type u_1} → [Field F] → [Field Omega] → [Algebra F Omega] →
(A : ValuationSubring Omega) → IsLocalRing.ResidueField ↥(A.comap (algebraMap F Omega)) →+* IsLocalRing.ResidueField ↥A`
(private diagnostic `73305fb7-fb85-4784-a297-c1e4858bc259`).

## Modifications

- The source namespace `LocalClassFieldTheory` is prefixed by `Langlands.NYLL`.
- Only this definition is extracted. Its section `PurelyInseparableComap`, the
  binders `{F Omega : Type u} [Field F] [Field Omega] [Algebra F Omega]`, the
  `universe u` declaration, the enclosing `noncomputable section`, the docstring,
  the `noncomputable` modifier and the definition body are retained unchanged.
  The body's local instance is the published theorem
  `Langlands.NYLL.LocalClassFieldTheory.valuationSubringComapMap_isLocalHom`,
  the adaptation of the source theorem the source body cites.
- The four source imports are replaced by the published module
  `Langlands.NYLL.ClassFieldTheory.LocalClassFieldTheory.Finite.LocalReciprocity.ResidueAlgebraicallyClosed.U003.Proofs`,
  which supplies M237.003 and, through its imports, M237.002. No other NYLL
  declaration is used.
- The source theorems that follow (M237.005, M237.006) are stated in the sibling
  `U004/Statements.lean`.

The original copyright and author header is retained. Apache-2.0 attribution
and notices are in `licenses/NYLL/LICENSE` and `licenses/NYLL/NOTICE`.
This support unit makes no claim to discharge the host class-formation, cup,
transfer, Tate or reciprocity targets.
