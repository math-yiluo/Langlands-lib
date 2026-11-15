# Surjectivity of Frobenius on a residue algebraic closure (proof)

This module proves the published target
`Langlands.NYLL.LocalClassFieldTheory.residueAbsoluteFrobenius_isAlgClosure_surjectiveStatement`
(M236.015, in `ResidueAlgebraicClosureDegree/Frobenius/Statements.lean`) by the theorem
`Langlands.NYLL.LocalClassFieldTheory.residueAbsoluteFrobenius_isAlgClosure_surjective`.

Adapted by Worker 5168 from Naganori Yamaguchi, ClassFieldTheory (NYLL), pinned commit
`fbd320cd8b1b06487c58227e92eb135794267709`. Registered source:
`external-lean-reuse-snapshots-2026-10-21`, fingerprint
`26e8c647ade044fe9bd4dd1f9d997d4ca12aaa4766e55ab31cb64ca9f8415e01`. The source files are under
`/home/taskhub/pilot/literature/External Lean project reuse survey- pinned source snapshots, 21 October 2026/n-yamaguchi-0729--ClassFieldTheory/source`.

| Unit | Original declaration, file and lines | Use here |
| --- | --- | --- |
| M236.015 | `residueAbsoluteFrobenius_isAlgClosure_surjective`, `ResidueAlgebraicClosureDegree.lean` 212–220 | the theorem (source proof kept) |
| M236.014 | `residueAbsoluteFrobeniusRangeIn_eq_top`, same file 203–210 | proved inside the theorem as `htop` |
| M236.013 | `fixedField_residueAbsoluteFrobeniusRangeIn`, same file 181–201 | proved inside the theorem as `hfixed` |
| M236.011 | `mem_range_algebraMap_iff_frobenius_fixed_in`, same file 145–170 (backward direction) | private lemma `u015_mem_range_algebraMap_of_pow_card` |
| M168.006 | `restrictNormalHom_residueAbsoluteFrobenius`, `ResidueAbsoluteFrobenius.lean` 115–124 | imported theorem `restrictNormalHom_residueAbsoluteFrobenius` |
| M168.007, M168.009 | `restrictNormalHom_residueAbsoluteFrobenius_one` (126–136), `residueAbsoluteFrobenius_one` (161–177), same file | replaced by the pointwise private lemma `u015_residueAbsoluteFrobenius_one_apply` |

Both source files are in `Nyll/ClassFieldTheory/LocalClassFieldTheory/Finite/LocalReciprocity/`.
Whole-file SHA-256: `ResidueAlgebraicClosureDegree.lean`
`650281a7282f345ec940ffcf4b5e7b794a2e18c6e34838a4def9649fe89ac2d5`, `ResidueAbsoluteFrobenius.lean`
`5f0290a3a451eb28a4e9c75bfeb419866744332e3c72da901891f3d1d9f1c82f`.

## Target

Under the source's `variable` blocks (lines 39–41 of `ResidueAlgebraicClosureDegree.lean`), the
theorem takes, in order, `k : Type u`, `[Field k]`, `[Fintype k]`, `Omega : Type v`,
`[Field Omega]`, `[Algebra k Omega]`, `[Algebra.IsAlgebraic k Omega]` and `[IsAlgClosed Omega]`.
Its type is `residueAbsoluteFrobenius_isAlgClosure_surjectiveStatement k Omega`, which is

```lean
haveI : IsAlgClosure k Omega := ⟨inferInstance, inferInstance⟩
haveI : IsGalois k Omega := {}
Function.Surjective (residueAbsoluteFrobenius k Omega)
```

So the canonical Frobenius homomorphism `residueAbsoluteFrobenius k Omega : ZHatMul →ₜ* (Omega ≃ₐ[k] Omega)`
(M168.005) on an algebraic closure `Omega` of the finite field `k` is surjective. The two `haveI`s
supply the values of the source's private instances M236.002 (`IsAlgClosure k Omega`) and M236.003
(`IsGalois k Omega`), as the Markdown of the target explains.

## Why the proof is self-contained

The source proof rewrites with M236.014, which rests on M236.013, M236.011 and M168.006–M168.009.
At the author's base these prerequisites were unavailable. The integrated module reuses the
published M168.006 restriction theorem and proves the remaining facts needed by its argument.
The two private lemmas carry the prefix `u015_` and add no public declaration, instance or
hypothesis. The main theorem depends on no unpublished result.

Imports: the published target module `ResidueAlgebraicClosureDegree/Frobenius/Statements`, which
brings in `residueAbsoluteFrobenius`, `residueFrobeniusToLimit`,
`finiteResidueFrobeniusIntermediate` and `residueAbsoluteFrobeniusRangeIn`; the published M167.013
proof module `FiniteResidueFrobenius/U013/Proofs` (`finiteResidueFrobeniusFromZHat_one`);
`ResidueAbsoluteFrobenius/U006/Proofs` (`restrictNormalHom_residueAbsoluteFrobenius`); and
`Mathlib.FieldTheory.Galois.Infinite` (`InfiniteGalois.fixingSubgroup_fixedField`).

## Implemented proof

### Reused restriction theorem and private lemmas

The imported restriction theorem and the first private lemma use the variables of the M168 source,
`(k : Type u) (Omega : Type v) [Field k] [Fintype k] [Field Omega] [Algebra k Omega] [IsGalois k Omega]`.

1. The imported `restrictNormalHom_residueAbsoluteFrobenius k Omega z E` (M168.006): for
   `z : ZHatMul` and a finite Galois intermediate field `E`,
   `AlgEquiv.restrictNormalHom E (residueAbsoluteFrobenius k Omega z) = finiteResidueFrobeniusIntermediate k Omega E z`.
   Its published proof is the source proof. `residueAbsoluteFrobenius` is the inverse of Mathlib's
   `InfiniteGalois.continuousMulEquivToLimit` applied to `residueFrobeniusToLimit k Omega z`.
   Apply `apply_symm_apply` and take the `op E` component of the inverse-limit element. The
   component of the limit equivalence at `E` is restriction to `E`, and the component of
   `residueFrobeniusToLimit` is `finiteResidueFrobeniusIntermediate k Omega E z`, so both sides
   agree by definition.

2. `u015_residueAbsoluteFrobenius_one_apply x`: for every `x : Omega`,
   `residueAbsoluteFrobenius k Omega (Multiplicative.ofAdd 1) x = x ^ Fintype.card k`. This is
   M168.009 applied to one point, proved directly instead of through the inverse limit. Let
   `E = FiniteGaloisIntermediateField.adjoin k {x}`, the normal closure of `k(x)`, which contains
   `x` by `FiniteGaloisIntermediateField.subset_adjoin`. By `AlgEquiv.restrictNormalHom_apply`, the
   value at `x` equals the value at `⟨x, hx⟩ : E` of the restriction to `E`. The imported theorem turns that
   restriction into `finiteResidueFrobeniusIntermediate k Omega E (ofAdd 1)`, which is by
   definition `finiteResidueFrobeniusFromZHat k E (ofAdd 1)` once `E` is known to be finite. The
   published M167.013 theorem `finiteResidueFrobeniusFromZHat_one` rewrites it to the arithmetic
   Frobenius `FiniteField.frobeniusAlgEquivOfAlgebraic k E`, whose value is `⟨x, hx⟩ ^ #k`
   (`FiniteField.coe_frobeniusAlgEquivOfAlgebraic`). Its coercion to `Omega` is `x ^ #k` by
   definition. The argument combines the source's M168.007 proof with this evaluation, so the
   source's M168.008 lemma `restrictNormalHom_frobeniusAlgEquivOfAlgebraic`
   (`ResidueAbsoluteFrobenius.lean` 138–159) is not needed.

3. `u015_mem_range_algebraMap_of_pow_card x hxpow` (the backward direction of M236.011, with the
   same proof): if `x : Omega` satisfies `x ^ #k = x`, then `x ∈ Set.range (algebraMap k Omega)`.
   The element `x` is a root of `p = X ^ #k - X ∈ k[X]`, which is nonzero
   (`FiniteField.X_pow_card_sub_X_ne_zero`) and splits over `k`
   (`FiniteField.isSplittingField_sub k k`). Then `Splits.image_rootSet` shows that the root set of
   `p` in `Omega` is the image of its root set in `k`. This lemma omits
   `[Algebra.IsAlgebraic k Omega]` and `[IsAlgClosed Omega]`, which it does not use.

### Main theorem

The proof first installs the target's two instances with local `have`s:
`IsAlgClosure k Omega := ⟨inferInstance, inferInstance⟩` and `IsGalois k Omega := {}`. These are
the same terms as the target's `haveI`s and as those inlined in the M236.012 definition
`residueAbsoluteFrobeniusRangeIn`. They are propositions, so any two instances agree. After
`show Function.Surjective (residueAbsoluteFrobenius k Omega)`, write `H` for
`residueAbsoluteFrobeniusRangeIn k Omega`, the closed subgroup whose underlying subgroup is by
definition the range of `(residueAbsoluteFrobenius k Omega).toMonoidHom`.

- `hfixed` (M236.013, source argument): `IntermediateField.fixedField H.toSubgroup = ⊥`. The
  inequality `≥` is `bot_le`. For `≤`, let `x` be fixed by `H`. The element
  `residueAbsoluteFrobenius k Omega (ofAdd 1)` lies in `H` (witness `ofAdd 1`, by definition of the
  range). So `x` is fixed by it, which by lemma 2 says `x ^ #k = x`. Lemma 3 gives
  `x ∈ Set.range (algebraMap k Omega)`, that is `x ∈ ⊥` (`IntermediateField.mem_bot`). The source
  instead rewrites the Frobenius element with M168.009 and uses M236.011 in the form "fixed by
  `FiniteField.frobeniusAlgEquivOfAlgebraic`".
- `htop` (M236.014, source proof): `H.toSubgroup = ⊤`. Mathlib's
  `InfiniteGalois.fixingSubgroup_fixedField H` says that the closed subgroup `H` is the fixing
  subgroup of its fixed field. Rewriting with `hfixed` and `IntermediateField.fixingSubgroup_bot`
  turns this into `⊤ = H.toSubgroup`.
- M236.015 (source proof): given `sigma : Omega ≃ₐ[k] Omega`, rewriting with `htop` turns
  `sigma ∈ H.toSubgroup` into `Subgroup.mem_top sigma`. Membership in the range is by definition a
  preimage `⟨z, residueAbsoluteFrobenius k Omega z = sigma⟩`, which closes the goal.

## Modifications

- The namespace is prefixed by `Langlands.NYLL`. The theorem's type is the published `Statement`
  rather than the restated proposition.
- The values of the private instances M236.002 and M236.003 come from local `have`s in the proof,
  not from the source's private section instances. M236.003 is built as `{}` from the local
  `IsAlgClosure` instance, because the source's `infer_instance` would use Mathlib's
  `IsAlgClosure.isGalois`, which needs `CharZero` in the pinned Mathlib.
- A `show` step unfolds the target before the proof.
- The source proof's rewrite with the theorem M236.014 is replaced by the local fact `htop`. That
  fact is proved from `hfixed`, the imported M168.006 theorem and two private lemmas,
  as described above. This retains the source arguments for the needed M236 and
  pointwise M168 facts. The only change of route
  is lemma 2, a pointwise form of M168.009 proved through one finite Galois subfield instead of the
  injectivity of the inverse-limit equivalence. It makes M168.008 unnecessary.
- Imports: the published modules listed above, in place of the NYLL source imports. The `open`
  commands are those of the published Frobenius modules: the source's, without
  `RamificationTheory.Field.absoluteGaloisGroup` (unused), plus `ClassFormation` for the
  profinite-integer names.

The original copyright and author header is retained. Apache-2.0 attribution and notices are in
`licenses/NYLL/LICENSE` and `licenses/NYLL/NOTICE`. Environment
`5c94c648-e8dc-4002-a50a-071ebf3f6096` (Lean 4.34.0, Mathlib
`5ed2965256430c3649e86755f9576b54eca72435`). The development check (Lake build) reports no errors
or warnings, and the theorem depends only on `propext`, `Classical.choice` and `Quot.sound`.
