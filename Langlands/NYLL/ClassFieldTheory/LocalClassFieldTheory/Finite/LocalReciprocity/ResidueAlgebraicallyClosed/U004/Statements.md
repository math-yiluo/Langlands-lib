# Target: residue fields of a purely inseparable extension

Adapted by Worker 172 from Naganori Yamaguchi, ClassFieldTheory, pinned commit
`fbd320cd8b1b06487c58227e92eb135794267709`, source
`Nyll/ClassFieldTheory/LocalClassFieldTheory/Finite/LocalReciprocity/ResidueAlgebraicallyClosed.lean`
(SHA-256 `86ae7eb949f70864a49e775bc93f8ab6bf45a6e72b75939ad830ded678d0b26b`).
Registered source: `external-lean-reuse-snapshots-2026-10-21`, fingerprint
`26e8c647ade044fe9bd4dd1f9d997d4ca12aaa4766e55ab31cb64ca9f8415e01`. The source file is readable under
`/home/taskhub/pilot/literature/External Lean project reuse survey- pinned source snapshots, 21 October 2026/n-yamaguchi-0729--ClassFieldTheory/source`.

| Unit | Original declaration and source lines | Library target or reused declaration |
| --- | --- | --- |
| M237.005 | `valuationSubringComapResidueMap_residue` (statement 139–145, proof 146) | not restated; covered by Mathlib `IsLocalRing.ResidueField.map_residue` (see below) |
| M237.006 | `valuationSubring_comap_residueField_isPurelyInseparable` (statement 148–160, proof 161–216) | `valuationSubring_comap_residueField_isPurelyInseparableStatement` (`def`, this file) |

Both sources are in section `PurelyInseparableComap` (binders at line 83). Original
names are in `LocalClassFieldTheory`; the target is in
`Langlands.NYLL.LocalClassFieldTheory`. It uses the definition
`valuationSubringComapResidueMap` (M237.004, sibling `U004/Definitions.lean`),
which is built from `valuationSubringComapMap` (M237.002,
`Initial/Definitions.lean`). Throughout, `B` abbreviates
`A.comap (algebraMap F Omega)`, the pulled-back valuation subring of `F`.

## Meaning of the target

`valuationSubring_comap_residueField_isPurelyInseparableStatement A` has the
section binders `{F Omega : Type u} [Field F] [Field Omega] [Algebra F Omega]`,
the hypothesis `[IsPurelyInseparable F Omega]` bound in its own signature, as the
source theorem does, and an explicit `A : ValuationSubring Omega`. It makes
`IsLocalRing.ResidueField A` an algebra over `IsLocalRing.ResidueField B` through
`(valuationSubringComapResidueMap A).toAlgebra` (a local `letI`, as in the source
statement) and asserts
`IsPurelyInseparable (IsLocalRing.ResidueField B) (IsLocalRing.ResidueField A)`.
So a purely inseparable field extension stays purely inseparable on residue
fields of a valuation ring and its pullback.

A `#check` of the elaborated declaration shows exactly
`{F Omega : Type u_1} → [Field F] → [Field Omega] → [Algebra F Omega] → [IsPurelyInseparable F Omega] → ValuationSubring Omega → Prop`.
In particular the `[IsPurelyInseparable F Omega]` hypothesis, which the
proposition does not mention, is kept because it is a binder of the declaration
itself, not a section variable. The same check compiled an `example` that
compares this type binder by binder with the source signature (private
diagnostic `3d4e12d7-8c17-428d-a160-2bf5a33da5c9`). The file asserts no proof.

## M237.005 is reused from Mathlib

The source theorem M237.005 states, for `x : B`,

`valuationSubringComapResidueMap A (IsLocalRing.residue B x) =
IsLocalRing.residue A (valuationSubringComapMap A x)`,

proved by `rfl`. Since `valuationSubringComapResidueMap A` is
`IsLocalRing.ResidueField.map (valuationSubringComapMap A)`, this is the instance
of Mathlib's `@[simp]` theorem
`IsLocalRing.ResidueField.map_residue (f : R →+* S) [IsLocalHom f] (r : R) :
ResidueField.map f (residue R r) = residue S (f r)`
for `f = valuationSubringComapMap A`. The required `IsLocalHom` instance is the
published theorem `valuationSubringComapMap_isLocalHom` (M237.003, module
`...ResidueAlgebraicallyClosed.U003.Proofs`), supplied locally with its type
written out: `have : IsLocalHom (valuationSubringComapMap (F := F) A) :=
valuationSubringComapMap_isLocalHom (F := F) A`. (The type ascription is needed
because the theorem's declared type is the target
`valuationSubringComapMap_isLocalHomStatement A`, which instance search does not
unfold.) A focused check compiled the source statement of M237.005 with its exact
binders, proved by `exact IsLocalRing.ResidueField.map_residue
(valuationSubringComapMap (F := F) A) x` after this `have`, and also in term mode
over all binders (private diagnostic `903db0c3-e3e4-4b82-be45-2590d1782bca`).
So M237.005 gets no target and no proof task here; consumers use
`IsLocalRing.ResidueField.map_residue` with that local instance. The M237.006
proof, which the source writes with `rw [valuationSubringComapResidueMap_residue]`,
will record the replacement in its own Markdown.

## Modifications

- The source namespace `LocalClassFieldTheory` is prefixed by `Langlands.NYLL`.
- The source theorem M237.006 is replaced by a Prop-valued `def` named with the
  suffix `Statement`. Its explicit argument and instance hypothesis are the
  source's, and its body is the source proposition unchanged. The implicit and
  instance binders come from the source's section `PurelyInseparableComap`
  variable line, which is retained. The source proof is omitted.
- M237.005 is not restated (see above).
- The `universe u` declaration and the enclosing `noncomputable section` are retained.
- The four source imports are replaced by the sibling definition module
  `...ResidueAlgebraicallyClosed.U004.Definitions` and
  `Mathlib.FieldTheory.PurelyInseparable.Basic` (for `IsPurelyInseparable`).
  No other NYLL declaration is used.

The original copyright and author header is retained. Apache-2.0 attribution
and notices are in `licenses/NYLL/LICENSE` and `licenses/NYLL/NOTICE`.
This support unit makes no claim to discharge the host class-formation, cup,
transfer, Tate or reciprocity targets.
