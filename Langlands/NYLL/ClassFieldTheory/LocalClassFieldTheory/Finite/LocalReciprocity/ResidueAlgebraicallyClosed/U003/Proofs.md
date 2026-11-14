# Proof: the pulled-back valuation-ring map is local

Adapted by Worker 172 from Naganori Yamaguchi, ClassFieldTheory, pinned commit
`fbd320cd8b1b06487c58227e92eb135794267709`, source
`Nyll/ClassFieldTheory/LocalClassFieldTheory/Finite/LocalReciprocity/ResidueAlgebraicallyClosed.lean`
(SHA-256 `86ae7eb949f70864a49e775bc93f8ab6bf45a6e72b75939ad830ded678d0b26b`).
Registered source: `external-lean-reuse-snapshots-2026-10-21`, fingerprint
`26e8c647ade044fe9bd4dd1f9d997d4ca12aaa4766e55ab31cb64ca9f8415e01`.

| Unit | Original declaration and source lines | Adapted declaration | Target proved |
| --- | --- | --- | --- |
| M237.003 | `LocalClassFieldTheory.valuationSubringComapMap_isLocalHom` (section binders 83, statement 96–97, proof 98–128) | `Langlands.NYLL.LocalClassFieldTheory.valuationSubringComapMap_isLocalHom` | `Langlands.NYLL.LocalClassFieldTheory.valuationSubringComapMap_isLocalHomStatement` |

The theorem has the section binders `{F Omega : Type u} [Field F] [Field Omega]
[Algebra F Omega]` and `(A : ValuationSubring Omega)`, and its type is
`valuationSubringComapMap_isLocalHomStatement (F := F) A`, which unfolds to
`IsLocalHom (valuationSubringComapMap (F := F) A)`.

## Proof

After `unfold valuationSubringComapMap_isLocalHomStatement`, the tactic proof is
the source proof unchanged. Let `x` be an element of `A.comap (algebraMap F Omega)`
whose image is a unit `u` of `A`.

1. `x ≠ 0` in `F`: otherwise its image is `0`, which is not a unit.
2. The inverse `(x : F)⁻¹` lies in the pullback: its image is
   `(algebraMap F Omega x)⁻¹ = (u : Omega)⁻¹`, which equals the value of the unit
   `u⁻¹` of `A` and so lies in `A`.
3. These give a unit of the pullback with value `x` (the two inverse laws hold
   by `Subtype.ext` and `x ≠ 0`), so `x` is a unit.

## Modifications

- Namespace prefixed by `Langlands.NYLL`; the theorem's type is the published
  target, unfolded as the first tactic step. The remaining proof, section
  `PurelyInseparableComap`, binders, `universe u`, `noncomputable section` and
  docstring are the source's.
- Imports: only the published `ResidueAlgebraicallyClosed.Initial.Statements`
  module, instead of the four source imports. The definition
  `valuationSubringComapMap` (M237.002) comes from the published
  `ResidueAlgebraicallyClosed.Initial.Definitions` module through that import.

- The source's section heading comment
  `/-! ## Residues under a purely inseparable ambient extension -/` (line 79) is
  not repeated; the published statement module carries it.
- Submitted by Worker 106 from Worker 172's public draft for Task 6030, with
  the Lean code unchanged apart from this submission note in the modification
  record.

The original copyright and author header is retained. Apache-2.0 attribution
and notices are in `licenses/NYLL/LICENSE` and `licenses/NYLL/NOTICE`.
This support unit makes no claim to discharge the host class-formation, cup,
transfer, Tate or reciprocity targets.
