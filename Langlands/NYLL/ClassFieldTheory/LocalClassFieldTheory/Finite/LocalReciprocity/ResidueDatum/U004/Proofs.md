# The index of a finite degree image (proof)

This module proves the published target
`Langlands.NYLL.LocalClassFieldTheory.Internal.residueDatumIn_fieldImage_index_closedFixingSubgroupStatement`
(M238.004, in [`ResidueDatum/Initial/Statements.lean`](../Initial/Statements.lean)) by the theorem
`Langlands.NYLL.LocalClassFieldTheory.Internal.residueDatumIn_fieldImage_index_closedFixingSubgroup`,
which keeps the source's `Internal.` name component.

Adapted by Worker 59 (draft) and Worker 737 (checked and submitted) from Naganori Yamaguchi, ClassFieldTheory (NYLL), pinned commit
`fbd320cd8b1b06487c58227e92eb135794267709`, source
[`Nyll/ClassFieldTheory/LocalClassFieldTheory/Finite/LocalReciprocity/ResidueDatum.lean`](https://github.com/n-yamaguchi-0729/ClassFieldTheory/blob/fbd320cd8b1b06487c58227e92eb135794267709/Nyll/ClassFieldTheory/LocalClassFieldTheory/Finite/LocalReciprocity/ResidueDatum.lean)
(121 lines, SHA-256 `0ffd3ceea309047d8e54275d4680c8c86ea3dd071ad786a71df35f18642bfbdf`),
theorem `Internal.residueDatumIn_fieldImage_index_closedFixingSubgroup` (M238.004, lines 109–118:
doc comment, signature 112–115, proof 116–118), under the section variables of lines 31–33.
Registered source: `external-lean-reuse-snapshots-2026-10-21`, fingerprint
`26e8c647ade044fe9bd4dd1f9d997d4ca12aaa4766e55ab31cb64ca9f8415e01`. The work is part of Task 5862.

## Target

The theorem takes, in order, `k Omega : Type`, `[Field k] [Fintype k] [Field Omega]
[Algebra k Omega] [Algebra.IsAlgebraic k Omega] [IsAlgClosed Omega]` (the source section
variables) and `E : FiniteGaloisIntermediateField k Omega`. Its type is
`Internal.residueDatumIn_fieldImage_index_closedFixingSubgroupStatement k Omega E`, which is

```lean
haveI : IsAlgClosure k Omega := ⟨inferInstance, inferInstance⟩
haveI : IsGalois k Omega := {}
((residueDatumIn k Omega).fieldImage
    (closedFixingSubgroup k Omega E)).index = Module.finrank k E
```

So the image of the subgroup fixing `E` under the residue degree of M238.001 `residueDatumIn` has
index `[E : k]` in `ZHatMul = Multiplicative ZHat`.

## Implemented proof

The proof installs the local instances `have : IsAlgClosure k Omega := ⟨inferInstance, inferInstance⟩`
and `have : IsGalois k Omega := {}`, which replace the source's private instances M236.002 and
M236.003 and are written exactly as the `haveI`s of the target, and restates the target with
`show`. Then it follows the source:

1. Rewrite the degree image with the published M238.003 theorem
   `Langlands.NYLL.LocalClassFieldTheory.residueDatumIn_fieldImage_closedFixingSubgroup` (module
   `ResidueDatum/U003/Proofs`): it is `(zHatMulNat n).toAddMonoidHom.range.toSubgroup` with
   `n = Module.finrank k E`. That theorem's type is its `Statement`, so the rewrite uses it through
   a `show … from` that states the equation with the local instances.
2. `AddSubgroup.index_toSubgroup` (Mathlib) identifies the index of the multiplicative copy with
   the index of the additive subgroup `n ℤ̂ = (zHatMulNat n).toAddMonoidHom.range`.
3. The published M009.011 theorem `Langlands.NYLL.ClassFormation.zHatMulNat_range_index` (module
   `GaloisCohomology/ProfiniteIntegers/ProfiniteInteger/U011/Proofs`) gives that index as `n`,
   with `n > 0` from `Module.finrank_pos`.

No global instance and no hypothesis is added; the theorem uses only published proofs.

## Modifications

- Namespaces prefixed by `Langlands.NYLL` (`Langlands.NYLL.LocalClassFieldTheory`, with
  `Langlands.NYLL.RamificationTheory` and `Langlands.NYLL.ClassFormation` open, as in the
  published `Statements` module). The theorem's type is the published `Statement` rather than
  the restated proposition.
- The source gets `IsGalois k Omega` from the private instance `residueAlgebraicClosureIsGalois`
  of its imported `ResidueAlgebraicClosureDegree.lean`. Here local `have`s supply the instances
  M236.002 and M236.003; M236.003 is built as `{}` from the local `IsAlgClosure` instance, because
  Mathlib's `IsAlgClosure.isGalois` needs `CharZero` in the pinned Mathlib.
- A `show` step unfolds the target, and the source's `rw [residueDatumIn_fieldImage_closedFixingSubgroup k Omega E, …]`
  uses that theorem through `show (equation) from …`, because its type is the M238.003
  `Statement`. The other rewrite and the final `exact` are the source's.
- Imports: the M238.003 proof module `ResidueDatum/U003/Proofs` (which imports the published
  `ResidueDatum/Initial/Statements`) and `GaloisCohomology/ProfiniteIntegers/ProfiniteInteger/U011/Proofs`,
  in place of the NYLL source imports.

The original copyright and author header is retained. Apache-2.0 attribution and notices are in
`licenses/NYLL/LICENSE` and `licenses/NYLL/NOTICE`. Environment
`5c94c648-e8dc-4002-a50a-071ebf3f6096` (Lean 4.34.0, Mathlib
`5ed2965256430c3649e86755f9576b54eca72435`).
