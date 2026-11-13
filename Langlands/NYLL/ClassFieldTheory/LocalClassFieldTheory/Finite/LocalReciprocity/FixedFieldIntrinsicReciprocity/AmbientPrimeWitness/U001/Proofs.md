# Transport of an identified abelianized prime value: proof

This module proves the published closed proposition
`Langlands.NYLL.LocalClassFieldTheory.abelianizationCongr_symm_eq_primeTargetStatement`
(NYLL source unit M284.001) by the theorem
`Langlands.NYLL.LocalClassFieldTheory.abelianizationCongr_symm_eq_primeTarget`.
Its only import is the statement module
`Langlands.NYLL.ClassFieldTheory.LocalClassFieldTheory.Finite.LocalReciprocity.FixedFieldIntrinsicReciprocity.AmbientPrimeWitness.U001.Statements`,
which imports only Mathlib's `Mathlib.GroupTheory.Abelianization.Defs`.
The statement pair and everything it imports are unchanged.

## Exact target

The theorem's type is exactly
`abelianizationCongr_symm_eq_primeTargetStatement`. Unfolded, it says:

```lean
∀ {Q₀ G₀ G : Type}
  [Group Q₀] [Group G₀] [Group G]
  (q₀ : Q₀ ≃* G₀) (qE : Q₀ ≃* G)
  (qAmbient : Q₀) (r : Additive (Abelianization G₀)),
  r = Additive.ofMul (q₀.abelianizationCongr (Abelianization.of qAmbient)) →
  qE.abelianizationCongr (q₀.abelianizationCongr.symm (Additive.toMul r)) =
    qE.abelianizationCongr (Abelianization.of qAmbient)
```

Here `MulEquiv.abelianizationCongr` is Mathlib's equivalence
`Abelianization Q₀ ≃* Abelianization G₀` induced by `q₀`. In words: if `r`
is the image of the class of `qAmbient` under the abelianized `q₀`, then
pulling `r` back along the abelianized `q₀` and pushing it forward along the
abelianized `qE` gives the image of the class of `qAmbient` under the
abelianized `qE`.

## Proof

After introducing the ten binders and naming the premise `hprime`, the
proof is the original one:

1. Apply `congrArg Additive.toMul` to `hprime`. By `change`, the result
   `hprimeMul` reads
   `Additive.toMul r = q₀.abelianizationCongr (Abelianization.of qAmbient)`
   (the composite `toMul (ofMul _)` reduces definitionally).
2. A two-step `calc`. First, rewrite the argument `Additive.toMul r` with
   `hprimeMul` under `q₀.abelianizationCongr.symm` and then under
   `qE.abelianizationCongr` (two `congrArg` applications). Second,
   `MulEquiv.symm_apply_apply` for `q₀.abelianizationCongr` cancels the
   inverse with the forward map, which leaves
   `qE.abelianizationCongr (Abelianization.of qAmbient)`.

The proof uses only Mathlib and has the standard axioms `propext`,
`Classical.choice` and `Quot.sound`.

## Original correspondence

The original is Naganori Yamaguchi's
[`n-yamaguchi-0729/ClassFieldTheory`](https://github.com/n-yamaguchi-0729/ClassFieldTheory/tree/fbd320cd8b1b06487c58227e92eb135794267709),
commit `fbd320cd8b1b06487c58227e92eb135794267709`, file
`Nyll/ClassFieldTheory/LocalClassFieldTheory/Finite/LocalReciprocity/FixedFieldIntrinsicReciprocity/AmbientPrimeWitness.lean`
(SHA-256
`e994e84e592e80c1452852d6b3ef89a36527c36b2ec64a84775628ff3695894d`),
theorem `abelianizationCongr_symm_eq_primeTarget`: docstring lines 29–30,
signature lines 31–47, proof lines 48–66.

Adaptation changes:

- The theorem gets the `Langlands.NYLL` namespace prefix and proves the
  published closed proposition instead of carrying the binders in its
  signature. The proof therefore starts with `intro`, which names the
  anonymous premise `hprime` as in the original.
- The tactic proof after the `intro` is the original proof, line for line.
- The single import replaces the original imports. The original
  `noncomputable section`, the namespace openings (unused here) and all
  other declarations of the module are omitted.

The registered source collection is
`external-lean-reuse-snapshots-2026-10-21`, fingerprint
`26e8c647ade044fe9bd4dd1f9d997d4ca12aaa4766e55ab31cb64ca9f8415e01`, under
`n-yamaguchi-0729--ClassFieldTheory/source/`. The attribution supplement is
`nyll-classfieldtheory-fbd320cd-supplement`, fingerprint
`a81005c3aceabc51e9193cdc643d4dd81dd9d496dca2a0cf0111ce610d5b0330`.

## Attribution

The Lean header keeps the original 2026 Naganori Yamaguchi copyright,
authorship line and Apache-2.0 notice, followed by a dated modification
record by Worker 56. This pair reuses the complete shared draft revision 1
by Worker 56 for Task 5989 (`b70857f0-bed6-4bf9-b9c0-c3f0d744cf81`).
Worker 339 verified the pinned source correspondence and checked the proof
in the assigned environment before submission. The retained
[LICENSE](../../../../../../../../../licenses/NYLL/LICENSE) and
[NOTICE](../../../../../../../../../licenses/NYLL/NOTICE) are unchanged.

No instance or simp attribute is installed. The development check reports
no errors or warnings.
