# Unit norms under compatible field equivalences: proof

This module proves the published closed proposition
`Langlands.NYLL.LocalClassFieldTheory.normUnits_mapEquivStatement` (NYLL
source unit M283.006) by the theorem
`Langlands.NYLL.LocalClassFieldTheory.normUnits_mapEquiv`. Its only import
is the statement module
`Langlands.NYLL.ClassFieldTheory.LocalClassFieldTheory.Finite.LocalReciprocity.FixedFieldIntrinsicReciprocity.AmbientPrimeNormTransport.U006.Statements`.
The statement pair and everything it imports are unchanged. The sibling
proposition `normClass_mapEquivStatement` of the same statement module belongs
to a separate proof task, with designated module
`Langlands.NYLL.ClassFieldTheory.LocalClassFieldTheory.Finite.LocalReciprocity.FixedFieldIntrinsicReciprocity.AmbientPrimeNormTransport.U007.Proofs`.

## Exact target

The theorem's type is exactly `normUnits_mapEquivStatement`. Unfolded, it
says:

```lean
∀ (F E F₀ E₀ : Type)
  [Field F] [Field E] [Field F₀] [Field E₀]
  [Algebra F E] [Algebra F₀ E₀]
  (phiF : F ≃+* F₀) (phiE : E ≃+* E₀),
  RingHom.comp (algebraMap F₀ E₀) phiF.toRingHom =
      RingHom.comp phiE.toRingHom (algebraMap F E) →
  ∀ (y : Eˣ),
    normUnits F₀ E₀ (Units.mapEquiv phiE.toMulEquiv y) =
      Units.mapEquiv phiF.toMulEquiv (normUnits F E y)
```

Here `normUnits K L : Lˣ →* Kˣ` is the published
`Langlands.NYLL.LocalFieldTheory.normUnits`, defined as
`Units.map (Algebra.norm K)`. In words: if the two ring equivalences
commute with the algebra maps, then taking the norm of a unit and
transporting it agrees with transporting the unit and then taking its norm.
The four fields lie in universe zero, as in the original. No finite-dimensionality
assumption is added: Mathlib's norm comparison also covers the convention that
the norm is one when there is no finite basis.

## Proof

After introducing the binders (the commutation premise is named `hcomm`),
the proof is the original one:

1. `Units.ext` reduces the equation of units to an equation of their
   values. By `change`, the goal is
   `Algebra.norm F₀ (phiE y) = phiF (Algebra.norm F y)`; this holds by
   unfolding `normUnits` as `Units.map (Algebra.norm _)` and the values of
   `Units.mapEquiv`.
2. Mathlib's `Algebra.norm_eq_of_equiv_equiv phiF phiE hcomm y` gives
   `Algebra.norm F y = phiF.symm (Algebra.norm F₀ (phiE y))`.
3. Apply the injective map `phiF.symm` to both sides of the goal and
   rewrite `phiF.symm (phiF _)` with `RingEquiv.symm_apply_apply`. The
   resulting goal is the symmetric form of step 2.

The proof uses only Mathlib and the published definition of `normUnits`.
It has the standard axioms `propext`, `Classical.choice` and `Quot.sound`.

## Original correspondence

The original is Naganori Yamaguchi's
[`n-yamaguchi-0729/ClassFieldTheory`](https://github.com/n-yamaguchi-0729/ClassFieldTheory/tree/fbd320cd8b1b06487c58227e92eb135794267709),
commit `fbd320cd8b1b06487c58227e92eb135794267709`, file
`Nyll/ClassFieldTheory/LocalClassFieldTheory/Finite/LocalReciprocity/FixedFieldIntrinsicReciprocity/AmbientPrimeNormTransport.lean`
(SHA-256
`b430f3810416cb42cc7c61df63be3691b219a5fe39c0bc7c0c2a74292298bfa0`),
theorem `LocalClassFieldTheory.normUnits_mapEquiv`: docstring lines
187–188, signature lines 189–199, proof lines 200–209.

Adaptation changes:

- The theorem gets the `Langlands.NYLL` namespace prefix and proves the
  published closed proposition instead of carrying the binders in its
  signature. The proof therefore starts with `intro`, which gives the
  premise its original name `hcomm`.
- The tactic proof after the `intro` is the original proof, line for line.
- The single import replaces the original imports
  `Mathlib.FieldTheory.Galois.Basic` and
  `Nyll.ClassFieldTheory.LocalClassFieldTheory.Finite.LocalReciprocity.FixedFieldIntrinsicReciprocity.EmbeddedFrobeniusTransport`.
  Mathlib's norm comparison is available transitively through the published
  norm definition imported by the statement module. The original
  `noncomputable section`, the namespace openings (not needed, since the
  proof never names `normUnits`) and all other declarations of the module
  are omitted.

The registered source collection is
`external-lean-reuse-snapshots-2026-10-21`, fingerprint
`26e8c647ade044fe9bd4dd1f9d997d4ca12aaa4766e55ab31cb64ca9f8415e01`, under
`n-yamaguchi-0729--ClassFieldTheory/source/`. The attribution supplement is
`nyll-classfieldtheory-fbd320cd-supplement`, fingerprint
`a81005c3aceabc51e9193cdc643d4dd81dd9d496dca2a0cf0111ce610d5b0330`.

## Attribution

The Lean header keeps the original 2026 Naganori Yamaguchi copyright,
authorship line and Apache-2.0 notice, followed by a dated modification
record by Worker 56. The retained
[LICENSE](../../../../../../../../../licenses/NYLL/LICENSE) and
[NOTICE](../../../../../../../../../licenses/NYLL/NOTICE) are unchanged.
Worker 340 reused Worker 56's shared draft without changing its Lean proof,
checked the cited source and license hashes, and clarified the scope and
imports in this Markdown on 13 November 2026.

No instance or simp attribute is installed. The development check reports
no errors or warnings.
