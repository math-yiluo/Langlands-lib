# `Langlands.AnthropicFLT.Definitions.Def_Compat_Mathlib430`

Ported for task `d5966ed9-d721-4463-8c08-eff6191a91b1` (Deligne–Henniart wild virtual stability on actual Weil representations), as the source of Herbrand's quotient theorem for ramification groups. Definition module (FLT `Definitions/`).

## Source and licence

Port of `Definitions/Def_Compat_Mathlib430.lean` from the Anthropic Lean formalisation of Fermat's Last Theorem (commit `6e837e75355538c7f80bab5b956861e86c4eacc2`; project literature folder "Anthropic - Fermat's Last Theorem - complete Lean source at 6e837e75355538c7f80bab5b956861e86c4eacc2", literature id `anthropic-flt-complete-lean-source-6e837e75`). The text is the FLT text except for the changes listed below.

Licence: Apache License, Version 2.0; Copyright 2026 Anthropic, PBC. Copies of the FLT `LICENSE`, `NOTICE` and `ATTRIBUTION.md` are in `licenses/Anthropic-FLT/` (added by statement artifact `a25bcdd5-03da-45b4-a0d3-100bb603e7c5`).

FLT `ATTRIBUTION.md` lists this file in §4 (Mathlib): it reproduces, under new names and without docstrings, Mathlib v4.30.0 text (commit `c5ea00351c28e24afc9f0f84379aa41082b1188f`, Apache-2.0) from eight Mathlib files, whose copyright holders and authors are listed there: `Mathlib/RepresentationTheory/Basic.lean` (Antoine Labelle), `Mathlib/RepresentationTheory/Rep/Basic.lean` (Yunzhou Xie; Edison Xie, Kim Morrison), `Mathlib/Algebra/Group/End.lean` (Johannes Hölzl; Johannes Hölzl, Callum Sutton, Yury Kudryashov), `Mathlib/Algebra/GroupWithZero/Action/Basic.lean` (Chris Hughes; Chris Hughes, Yury Kudryashov), `Mathlib/Algebra/Ring/AddAut.lean` (Yury Kudryashov), `Mathlib/Algebra/Ring/Action/Submonoid.lean` (David Ang), `Mathlib/NumberTheory/EllipticDivisibilitySequence.lean` (David Kurniadi Angdinata) and `Mathlib/NumberTheory/RamificationInertia/Galois.lean` (Yongle Hu; Yongle Hu, Jiedong Jiang). The file's own Mathlib provenance comment is kept.

## Changes against the FLT file

- The FLT lakefile options are inserted after the imports: `maxHeartbeats 4000000`, `synthInstance.maxHeartbeats 400000`, `backward.isDefEq.respectTransparency.types false`.
- An attribution header comment is added at the top of the file.
- In the proof of `Representation.ofMulActionFinsupp_apply` the `simp only` lemmas `Finsupp.mapDomain_apply, hg` become `Finsupp.mapDomain_apply_of_injective hg` (the pinned Mathlib's name for the injective case).
- No other change: apart from these patches the declarations, statements and proofs are the FLT text.

## Content

FLT's compatibility file: Mathlib v4.30.0 declarations whose form changed in later Mathlib, re-declared under new
names (suffix `Finsupp` or a trailing prime) so that they do not clash with the current Mathlib. The file comments
(kept) name the Mathlib v4.30.0 source of each block. Of all of this, the Herbrand port uses only Block G
(`Ideal.card_inertia_eq_ramificationIdxIn'`, used by
`P2M.Sol.S_card_lowerRamificationGroup_zero_eq_ramificationIdxIn`); the file is ported whole.

- Block A (Mathlib `RepresentationTheory/Basic.lean`): the permutation representation
  `Representation.ofMulActionFinsupp k G H` on `H →₀ k`, the abbreviations `leftRegularFinsupp` and
  `diagonalFinsupp`, `ofMulActionFinsupp_def`, `ofMulActionFinsupp_single`.
- Block B: `Representation.ofMulActionFinsupp_apply` (`(ρ g f) h = f (g⁻¹ • h)`), and the bridging equivalence
  `Representation.ofMulActionFinsuppEquiv` with Mathlib's `Representation.ofMulAction` (FLT's own declaration).
- Block C (Mathlib `RepresentationTheory/Rep/Basic.lean`): `Rep.ofMulActionFinsupp`, `Rep.leftRegularFinsupp`,
  `Rep.diagonalFinsupp`, the isomorphism `Rep.ofMulActionFinsuppIso` with `Rep.ofMulAction` (FLT's own),
  `Rep.leftRegularHomFinsupp` and `Rep.leftRegularHomFinsupp_hom_single`. Four lines carry FLT's `-- [port]` marks
  (`noncomputable` added).
- Block D (Mathlib `Algebra/Group/End.lean`, `GroupWithZero/Action/Basic.lean`, `Ring/AddAut.lean`): an anonymous
  instance `Group (AddAut A)` (multiplication is composition), the primed lemmas `AddAut.coe_mul'` …
  `AddAut.apply_inv_self'`, three `example`s checking that `*`, `1` and `⁻¹` agree definitionally with `+`, `0`
  and `-` of the additive group structure of current Mathlib, `DistribMulAction.toAddAut'` (tagged `@[simps]`) and
  `AddAut.mulLeft'` (tagged `@[simps! +simpRhs]`), whose generated `simps` lemmas are not listed below, the
  instances `AddAut.applyDistribMulAction'` and `AddAut.apply_faithfulSMul'`, and `AddAut.smul_def'`.
- Block E (Mathlib `NumberTheory/EllipticDivisibilitySequence.lean`): the predicates `IsEllSequence'`,
  `IsDivSequence'`, `IsEllDivSequence'` on `W : ℤ → R` with the lemmas for `id` and for scalar multiples.
- Block F (Mathlib `Algebra/Ring/Action/Submonoid.lean`): the notation `α ^+ M` for `FixedPoints.addSubgroup M α`.
- Block G (adapted and re-proved from Mathlib `NumberTheory/RamificationInertia/Galois.lean`, for a finite Galois
  group `G` of `S` over `R` (`IsGaloisGroup G R S`), a maximal ideal `p` of `R` and a maximal ideal `P` over it with
  separable residue field extension): `Ideal.card_stabilizer_eq_card_inertia_mul_finrank'`
  (`|Stab(P)| = |inertia| · [S/P : R/p]`), `Ideal.ncard_primesOver_mul_card_inertia_mul_finrank'`
  (`#primes over p · |inertia| · [S/P : R/p] = |G|`), and for Dedekind domains with `S` finite and torsion-free
  over `R` and `p ≠ ⊥`: `Ideal.card_inertia_eq_ramificationIdxIn'` (`|inertia G P| = p.ramificationIdxIn S`) and
  `Ideal.card_stabilizer_eq'` (`|Stab(P)| = e · f`).

There are 3 further `example` checks outside section `Gates`.

## Declarations

Names, namespaces and statements are the FLT ones.

- def `Representation.ofMulActionFinsupp`
- abbrev `Representation.leftRegularFinsupp`
- abbrev `Representation.diagonalFinsupp`
- theorem `Representation.ofMulActionFinsupp_def`
- theorem `Representation.ofMulActionFinsupp_single`
- theorem `Representation.ofMulActionFinsupp_apply`
- def `Representation.ofMulActionFinsuppEquiv`
- abbrev `Rep.ofMulActionFinsupp`
- abbrev `Rep.leftRegularFinsupp`
- abbrev `Rep.diagonalFinsupp`
- def `Rep.ofMulActionFinsuppIso`
- abbrev `Rep.leftRegularHomFinsupp`
- theorem `Rep.leftRegularHomFinsupp_hom_single`
- anonymous instance `Group (AddAut A)` (namespace `AddAut`)
- theorem `AddAut.coe_mul'`
- theorem `AddAut.coe_one'`
- theorem `AddAut.coe_inv'`
- theorem `AddAut.mul_def'`
- theorem `AddAut.one_def'`
- theorem `AddAut.inv_def'`
- theorem `AddAut.mul_apply'`
- theorem `AddAut.one_apply'`
- theorem `AddAut.inv_symm'`
- theorem `AddAut.symm_inv'`
- theorem `AddAut.inv_apply'`
- theorem `AddAut.inv_apply_self'`
- theorem `AddAut.apply_inv_self'`
- def `DistribMulAction.toAddAut'`
- def `AddAut.mulLeft'`
- instance `AddAut.applyDistribMulAction'`
- theorem `AddAut.smul_def'`
- instance `AddAut.apply_faithfulSMul'`
- def `IsEllSequence'`
- def `IsDivSequence'`
- def `IsEllDivSequence'`
- lemma `isEllSequence'_id`
- lemma `isDivSequence'_id`
- theorem `isEllDivSequence'_id`
- lemma `IsEllSequence'.smul`
- lemma `IsDivSequence'.smul`
- lemma `IsEllDivSequence'.smul`
- theorem `Ideal.card_stabilizer_eq_card_inertia_mul_finrank'`
- lemma `Ideal.ncard_primesOver_mul_card_inertia_mul_finrank'`
- lemma `Ideal.card_inertia_eq_ramificationIdxIn'`
- lemma `Ideal.card_stabilizer_eq'`

## Dependencies

Ported FLT modules imported: none.
Other imports: `Mathlib.RepresentationTheory.Rep.Basic`, `Mathlib.Algebra.Group.End`, `Mathlib.Algebra.GroupWithZero.Action.Basic`, `Mathlib.Algebra.Ring.AddAut`, `Mathlib.Algebra.Ring.Action.Submonoid`, `Mathlib.NumberTheory.RamificationInertia.Galois`, `Mathlib.RingTheory.Invariant.Galois`, `Mathlib.FieldTheory.Galois.Basic`, `Mathlib.Tactic.LinearCombination`, `Mathlib.Tactic.Ring`.
