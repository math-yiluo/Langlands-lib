# Finite residue Frobenius exponent homomorphism and profinite action

Adapted by Worker 123 from Naganori Yamaguchi, ClassFieldTheory (NYLL), pinned commit
`fbd320cd8b1b06487c58227e92eb135794267709`, source
`Nyll/ClassFieldTheory/LocalClassFieldTheory/Finite/LocalReciprocity/FiniteResidueFrobenius.lean`.
Registered source: `external-lean-reuse-snapshots-2026-10-21`, fingerprint
`26e8c647ade044fe9bd4dd1f9d997d4ca12aaa4766e55ab31cb64ca9f8415e01`. The source file is readable under
`/home/taskhub/pilot/literature/External Lean project reuse survey- pinned source snapshots, 21 October 2026/n-yamaguchi-0729--ClassFieldTheory/source`.

| Unit | Original declaration and source lines | Adapted declaration |
| --- | --- | --- |
| M167.001 (private) | `finiteResidueFrobeniusIntegerPowers` (39–43) | inlined in `finiteResidueFrobeniusExponentHom` |
| M167.002 (private) | `finiteResidueFrobeniusIntegerPowers_degree_eq_zero` (45–53) | inlined in `finiteResidueFrobeniusExponentHom` |
| M167.003 | `finiteResidueFrobeniusExponentHom` (55–62) | `finiteResidueFrobeniusExponentHom` |
| M167.011 | `finiteResidueFrobeniusFromZHat` (133–148) | `finiteResidueFrobeniusFromZHat` |

Every unqualified original name above is in `LocalClassFieldTheory`; every
adapted name is in `Langlands.NYLL.LocalClassFieldTheory` unless fully qualified.
`ZHat`, `ZHatMul` and `zHatReduction` are the published
`Langlands.NYLL.ClassFormation` declarations.

## Content

Throughout, `k : Type u` is a field with `[Fintype k]` and `L : Type v` is a
finite field with `[Finite L]` and a `k`-algebra structure (source `variable`
block, lines 36–37, retained verbatim).

- `finiteResidueFrobeniusExponentHom k L :
  Multiplicative (ZMod (Module.finrank k L)) →* (L ≃ₐ[k] L)` is the
  multiplicative form of the additive map `ZMod [L : k] → Additive Gal(L/k)`
  obtained with `ZMod.lift` from the integer powers `m ↦ Frob^m` of the
  arithmetic Frobenius `FiniteField.frobeniusAlgEquivOfAlgebraic k L`
  (`x ↦ x ^ #k`). The integer-power map is factored through `ZMod [L : k]`
  because `Frob^[L : k] = 1`, which follows from
  `FiniteField.orderOf_frobeniusAlgEquivOfAlgebraic`.
- `finiteResidueFrobeniusFromZHat k L : ZHatMul →ₜ* (L ≃ₐ[k] L)` sends a
  profinite exponent `z` to `finiteResidueFrobeniusExponentHom k L` applied to
  the reduction `zHatReduction [L : k] _ z` of `z` modulo `[L : k]`; it is
  continuous because the Galois group of a finite extension is discrete.

## Modifications

- Namespace `LocalClassFieldTheory` becomes `Langlands.NYLL.LocalClassFieldTheory`;
  `open ClassFormation` now opens the published
  `Langlands.NYLL.ClassFormation` namespace.
- The private M167.001 definition (the homomorphism
  `zmultiplesHom (Additive (L ≃ₐ[k] L)) (Additive.ofMul (FiniteField.frobeniusAlgEquivOfAlgebraic k L))`)
  and the private M167.002 proof that it vanishes at `[L : k]` are written in
  place, as the value and the proof component of the subtype argument of
  `ZMod.lift`, in the body of `finiteResidueFrobeniusExponentHom`, their only
  use among the adapted rows. The proof is the source proof of M167.002
  unchanged. No `PortInternal` declaration is introduced. The resulting body is
  the source body with both private constants unfolded.
- The source imports `Mathlib.SetTheory.Cardinal.Finite` and the NYLL module
  `Nyll.ClassFieldTheory.AbstractClassFieldTheory.Degree.Fields` are replaced by
  the published `Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Degree.Fields.Definitions`
  (which supplies `ZHatMul` and, through its imports, `ZHat` and
  `zHatReduction`); the Mathlib imports `Mathlib.FieldTheory.Finite.Extension`
  and `Mathlib.FieldTheory.Galois.Profinite` are retained.
- The source theorems of the module are not in this file: their targets are in
  the sibling `Statements` module. The data command M167.008
  `finiteResidueFrobeniusExponentEquiv`, whose body needs the proofs of M167.006
  and M167.007, is not part of this module.
- Types, bodies, the `noncomputable section`, universes and binder order are
  otherwise retained. No instance is declared.

The original copyright and author header is retained. Apache-2.0 attribution
and notices are in `licenses/NYLL/LICENSE` and `licenses/NYLL/NOTICE`.
This support unit makes no claim to discharge the host class-formation, cup,
transfer, Tate or reciprocity targets.
