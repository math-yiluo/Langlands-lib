# Proof: residue fields of a purely inseparable extension

Adapted by Worker 172 from Naganori Yamaguchi, ClassFieldTheory, pinned commit
`fbd320cd8b1b06487c58227e92eb135794267709`, source
`Nyll/ClassFieldTheory/LocalClassFieldTheory/Finite/LocalReciprocity/ResidueAlgebraicallyClosed.lean`
(SHA-256 `86ae7eb949f70864a49e775bc93f8ab6bf45a6e72b75939ad830ded678d0b26b`).
Registered source: `external-lean-reuse-snapshots-2026-10-21`, fingerprint
`26e8c647ade044fe9bd4dd1f9d997d4ca12aaa4766e55ab31cb64ca9f8415e01`.

| Unit | Original declaration and source lines | Adapted declaration | Target proved |
| --- | --- | --- | --- |
| M237.006 | `LocalClassFieldTheory.valuationSubring_comap_residueField_isPurelyInseparable` (section binders 83, statement 148–160, proof 161–216) | `Langlands.NYLL.LocalClassFieldTheory.valuationSubring_comap_residueField_isPurelyInseparable` | `Langlands.NYLL.LocalClassFieldTheory.valuationSubring_comap_residueField_isPurelyInseparableStatement` |

The theorem has the section binders `{F Omega : Type u} [Field F] [Field Omega]
[Algebra F Omega]`, the hypothesis `[IsPurelyInseparable F Omega]` and
`(A : ValuationSubring Omega)`. Its type is
`valuationSubring_comap_residueField_isPurelyInseparableStatement (F := F) A`.
Write `B = A.comap (algebraMap F Omega)` and `k_B`, `k_A` for the residue fields
of `B` and `A`. The target unfolds to: with the algebra structure on `k_A` over
`k_B` given by `barI = valuationSubringComapResidueMap A` (M237.004),
`IsPurelyInseparable k_B k_A`.

## Proof

After `unfold valuationSubring_comap_residueField_isPurelyInseparableStatement`,
the proof first records the residue equation `hres : ∀ x : B,
valuationSubringComapResidueMap A (residue B x) = residue A
(valuationSubringComapMap A x)`. This is M237.005, which is not ported: `hres`
is proved by Mathlib's `IsLocalRing.ResidueField.map_residue
(valuationSubringComapMap A)` after `have : IsLocalHom (valuationSubringComapMap
A) := valuationSubringComapMap_isLocalHom A` (the published M237.003 theorem,
with its type written out so that instance search sees it). The rest is the
source proof, with `rw [hres]` in place of the source's two
`rw [valuationSubringComapResidueMap_residue]` steps. It introduces `B`, `barI` and
the algebra `barI.toAlgebra` as local definitions, takes an exponential
characteristic `q` of `F` (`ExpChar.exists F`) and splits on the two
constructors of `ExpChar F q`. In both cases it uses Mathlib's criterion
`isPurelyInseparable_iff_pow_mem`: for an exponential characteristic `p` of
`k_B`, `k_A` is purely inseparable over `k_B` iff for every `y : k_A` some
`y ^ (p ^ n)` lies in the image of `k_B`. Every `y` is the residue of some
`a : A` (`IsLocalRing.residue_surjective`).

1. **Characteristic zero** (the `ExpChar.zero` constructor, so `q = 1` and `F`
   has `CharZero`). Then `Algebra.IsSeparable F Omega` is found by instance
   search, so `Omega` is separable as well as purely inseparable over `F` and
   `algebraMap F Omega` is surjective
   (`IsPurelyInseparable.surjective_algebraMap_of_isSeparable`). Choose `z : F`
   with `algebraMap F Omega z = a`. Then `z ∈ B` because its image `a` lies in
   `A`; call this element `zB`. The criterion is applied with
   `p = ringExpChar k_B`, not with `q`: the residue field `k_B` may have prime
   characteristic although `F` has characteristic zero. With exponent `n = 0`
   the power `y ^ (p ^ 0)` is `y` itself (`pow_zero`, `pow_one`),
   and `barI (residue zB) = residue (valuationSubringComapMap A zB) = residue a`
   by `hres` and `Subtype.ext`.
2. **Prime characteristic** (the `ExpChar.prime` constructor, so `q` is prime
   and `F` has characteristic `q`). The characteristic `q` passes to
   `Omega` (injective `algebraMap`), to `A` (injective subtype), to `k_A`
   (`CharP.of_ringHom_of_ne_zero` along the residue map, as `q ≠ 0`) and to
   `k_B` (the field homomorphism `barI` is injective), so `q` is also the
   exponential characteristic of `k_B`, and the criterion is applied with
   `p = q`. Since `Omega` is purely inseparable over
   `F`, `IsPurelyInseparable.pow_mem` gives `n` and `z : F` with
   `algebraMap F Omega z = a ^ (q ^ n)`. Then `z ∈ B` since `a ^ (q ^ n) ∈ A`;
   call this `zB`. By `hres` and `map_pow`,
   `barI (residue zB) = residue (a ^ (q ^ n)) = (residue a) ^ (q ^ n) = y ^ (q ^ n)`.

## Modifications

- Namespace prefixed by `Langlands.NYLL`. The theorem's type is the published
  target, unfolded as the first tactic step. The remaining proof, section
  `PurelyInseparableComap`, binders, `universe u`, `noncomputable section` and
  docstring are the source's.
- M237.005 replacement: the source's simp lemma
  `valuationSubringComapResidueMap_residue` is not ported (it is Mathlib's
  `IsLocalRing.ResidueField.map_residue`, see `U004/Statements.md`). The proof
  adds the local equation `hres` described above and rewrites with it in the
  two places where the source rewrites with that lemma.
- Imports: only the published `ResidueAlgebraicallyClosed.U004.Statements`
  module, instead of the four source imports. It supplies the target and,
  through its imports, the definitions `valuationSubringComapMap` (M237.002) and
  `valuationSubringComapResidueMap` (M237.004) and the theorem
  `valuationSubringComapMap_isLocalHom` (M237.003). The Mathlib results used
  (`isPurelyInseparable_iff_pow_mem`, `IsPurelyInseparable.pow_mem`,
  `IsPurelyInseparable.surjective_algebraMap_of_isSeparable`) come from
  `Mathlib.FieldTheory.PurelyInseparable.Basic`, imported by `U004/Statements`;
  `IsLocalRing.ResidueField.map_residue` is in
  `Mathlib.RingTheory.LocalRing.ResidueField.Basic`.
- The source's section heading comment
  `/-! ## Residues under a purely inseparable ambient extension -/` (line 79) is
  not repeated; the published `Initial/Statements` module carries it.

Submitted by Worker 106 from Worker 172's public draft for Task 6927; the
Lean code is unchanged from that draft apart from a matching submission note
in its modification record. Worker 106 corrected the proof outline above after
review: the characteristic-zero case has exponential characteristic `q = 1`,
and the criterion's exponent base `p` is named separately from `q`.

The original copyright and author header is retained. Apache-2.0 attribution
and notices are in `licenses/NYLL/LICENSE` and `licenses/NYLL/NOTICE`.
This support unit makes no claim to discharge the host class-formation, cup,
transfer, Tate or reciprocity targets.
