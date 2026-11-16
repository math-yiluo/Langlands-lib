# The degree image of a finite fixing subgroup (proof)

This module proves the published target
`Langlands.NYLL.LocalClassFieldTheory.residueDatumIn_fieldImage_closedFixingSubgroupStatement`
(M238.003, in [`ResidueDatum/Initial/Statements.lean`](../Initial/Statements.lean)) by the theorem
`Langlands.NYLL.LocalClassFieldTheory.residueDatumIn_fieldImage_closedFixingSubgroup`.

Adapted by Worker 59 from Naganori Yamaguchi, ClassFieldTheory (NYLL), pinned commit
`fbd320cd8b1b06487c58227e92eb135794267709`, source
[`Nyll/ClassFieldTheory/LocalClassFieldTheory/Finite/LocalReciprocity/ResidueDatum.lean`](https://github.com/n-yamaguchi-0729/ClassFieldTheory/blob/fbd320cd8b1b06487c58227e92eb135794267709/Nyll/ClassFieldTheory/LocalClassFieldTheory/Finite/LocalReciprocity/ResidueDatum.lean)
(121 lines, SHA-256 `0ffd3ceea309047d8e54275d4680c8c86ea3dd071ad786a71df35f18642bfbdf`):
the private theorem `mem_fixingSubgroup_iff_restrictNormalHom_eq_one` (M238.002, lines 41–63)
and the theorem `residueDatumIn_fieldImage_closedFixingSubgroup` (M238.003, lines 65–107: doc
comment, signature 67–71, proof 72–107), under the section variables of lines 31–33. Registered
source: `external-lean-reuse-snapshots-2026-10-21`, fingerprint
`26e8c647ade044fe9bd4dd1f9d997d4ca12aaa4766e55ab31cb64ca9f8415e01`. The work is part of Task 5862.
Worker 736 checked this draft unchanged against Library `72480b70` and submits it for Task 7176.

## Target

The theorem takes, in order, `k Omega : Type`, `[Field k] [Fintype k] [Field Omega]
[Algebra k Omega] [Algebra.IsAlgebraic k Omega] [IsAlgClosed Omega]` (the source section
variables) and `E : FiniteGaloisIntermediateField k Omega`. Its type is
`residueDatumIn_fieldImage_closedFixingSubgroupStatement k Omega E`, which is

```lean
haveI : IsAlgClosure k Omega := ⟨inferInstance, inferInstance⟩
haveI : IsGalois k Omega := {}
(residueDatumIn k Omega).fieldImage
    (closedFixingSubgroup k Omega E) =
  (zHatMulNat (Module.finrank k E)).toAddMonoidHom.range.toSubgroup
```

So when `n = [E : k]`, the residue degrees (M238.001 `residueDatumIn`, whose degree map is
M236.017 `residueAbsoluteDegreeIn`) of the automorphisms of `Omega` fixing `E` are exactly the
elements of `n ℤ̂`, viewed as a subgroup of `ZHatMul = Multiplicative ZHat`.

## The private lemma M238.002

The source's private theorem is kept, with its source name, `omit` line, binders and proof, as a
`private theorem` of this module. It is not a public declaration and has no separate target, as
the task allows. It says that for an intermediate field `E` that is finite Galois over `k`, an
automorphism `sigma` of `Omega` fixes `E` pointwise
(`sigma ∈ E.toIntermediateField.fixingSubgroup`) if and only if its restriction
`AlgEquiv.restrictNormalHom E sigma` is the identity of `E`. Forward: the restriction agrees with
`sigma` on `E` (`AlgEquiv.restrictNormalHom_apply`), and `sigma` fixes every element of `E`.
Backward: evaluate the identity `restrictNormalHom E sigma = 1` at `⟨x, hx⟩ : E` and take
underlying values.

## Implemented proof

The proof first installs local instances with `have : IsAlgClosure k Omega` and
`have : IsGalois k Omega := {}`. These are the values of the source's private instances
M236.002 and M236.003, which the source file obtains from its import, and the same values the
target uses. A `show` then restates the target without the two `haveI`s, the instances now being
the local ones (definitionally the same). It sets `let : Finite E := Module.finite_of_finite k`.
The rest is the source proof, by extensionality in `z : ZHatMul`.

1. (`⊆`) An element of the image is `residueAbsoluteDegreeIn k Omega sigma` for some `sigma` in
   `closedFixingSubgroup k Omega E`, the subgroup fixing `E`. By the published M009.010 theorem
   `Langlands.NYLL.ClassFormation.zHatMulNat_range_eq_ker_reduction` (module
   `GaloisCohomology/ProfiniteIntegers/ProfiniteInteger/U010/Proofs`), `n ℤ̂` is the kernel of
   reduction modulo `n` (`zHatReduction n`), so it suffices to show that the reduction of the
   degree of `sigma` is `0`. M238.002 gives `AlgEquiv.restrictNormalHom E sigma = 1`. The
   published M236.022 theorem `finiteResidueFrobeniusExponentEquiv_symm_restrict_in` (module
   `ResidueAlgebraicClosureDegree/U022/Proofs`) says that the finite Frobenius coordinate of this
   restriction is that reduction (as `Multiplicative.ofAdd`). Its `Statement` type is unfolded
   with `unfold … at hcoordinate`; rewriting the restriction to `1` and using `map_one` gives
   `1 = Multiplicative.ofAdd (reduction)`, and `Multiplicative.toAdd` turns it into the claim.
2. (`⊇`) Let `z.toAdd` lie in `n ℤ̂`, so its reduction modulo `n` is `0`, again by M009.010. The
   preimage is `residueAbsoluteFrobenius k Omega z` (M168.005). It fixes `E`: by M238.002 it
   suffices that its restriction to `E` is `1`. The published M168.006 theorem
   `restrictNormalHom_residueAbsoluteFrobenius` (module `ResidueAbsoluteFrobenius/U006/Proofs`)
   rewrites the restriction as `finiteResidueFrobeniusIntermediate k Omega E z`, which is by
   definition `finiteResidueFrobeniusFromZHat k E z`. The published M167.012 theorem
   `finiteResidueFrobeniusFromZHat_apply` (module `FiniteResidueFrobenius/U012/Proofs`) rewrites
   this as `finiteResidueFrobeniusExponentHom k E` applied to `Multiplicative.ofAdd` of the
   reduction of `z.toAdd`, which is `0`, so the value is `1` by `map_one`. Its degree is `z`,
   because `residueAbsoluteDegreeIn` is the inverse of `residueAbsoluteFrobeniusEquivIn`
   (M236.016), whose forward map is `residueAbsoluteFrobenius`:
   `(residueAbsoluteFrobeniusEquivIn k Omega).symm_apply_apply z`.

No global instance and no hypothesis is added; the theorem uses only published proofs.

## Modifications

- Namespaces prefixed by `Langlands.NYLL` (`Langlands.NYLL.LocalClassFieldTheory`, with
  `Langlands.NYLL.RamificationTheory` and `Langlands.NYLL.ClassFormation` open, as in the
  published `Statements` module). The theorem's type is the published `Statement` rather than
  the restated proposition.
- The source gets `IsGalois k Omega`, which `closedFixingSubgroup` needs, from the private instance
  `residueAlgebraicClosureIsGalois` of its imported `ResidueAlgebraicClosureDegree.lean`. Here
  local `have`s supply the instances M236.002 and M236.003. M236.003 is built as `{}` from the
  local `IsAlgClosure` instance, because Mathlib's `IsAlgClosure.isGalois` needs `CharZero` in the
  pinned Mathlib.
- A `show` step unfolds the target before the source script, and one
  `unfold finiteResidueFrobeniusExponentEquiv_symm_restrict_inStatement at hcoordinate` is added
  before the source's `rw … at hcoordinate`, because the published M236.022 theorem has the
  `Statement` as its type. The rest of the source proof script and the M238.002 proof are
  unchanged.
- The private M238.002 is kept as a private theorem of this proof module (see above).
- Imports: the published modules `ResidueDatum/Initial/Statements`,
  `ResidueAlgebraicClosureDegree/U022/Proofs`, `ResidueAbsoluteFrobenius/U006/Proofs`,
  `FiniteResidueFrobenius/U012/Proofs` and `GaloisCohomology/ProfiniteIntegers/ProfiniteInteger/U010/Proofs`,
  in place of the NYLL source imports.

The original copyright and author header is retained. Apache-2.0 attribution and notices are in
`licenses/NYLL/LICENSE` and `licenses/NYLL/NOTICE`. Environment
`5c94c648-e8dc-4002-a50a-071ebf3f6096` (Lean 4.34.0, Mathlib
`5ed2965256430c3649e86755f9576b54eca72435`).
