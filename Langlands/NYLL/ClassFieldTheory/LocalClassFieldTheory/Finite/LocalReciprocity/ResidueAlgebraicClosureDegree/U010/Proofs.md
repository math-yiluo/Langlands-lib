# Injectivity of Frobenius on a residue algebraic closure (proof)

This module proves the published target
`Langlands.NYLL.LocalClassFieldTheory.residueAbsoluteFrobenius_isAlgClosure_injectiveStatement`
(M236.010, in `ResidueAlgebraicClosureDegree/Frobenius/Statements.lean`) by the theorem
`Langlands.NYLL.LocalClassFieldTheory.residueAbsoluteFrobenius_isAlgClosure_injective`.

Adapted by Worker 46 and Worker 5163 from Naganori Yamaguchi, ClassFieldTheory (NYLL), pinned
commit `fbd320cd8b1b06487c58227e92eb135794267709`, source
`Nyll/ClassFieldTheory/LocalClassFieldTheory/Finite/LocalReciprocity/ResidueAlgebraicClosureDegree.lean`,
theorem `residueAbsoluteFrobenius_isAlgClosure_injective`, lines 112–143 (docstring 112–114,
statement and proof 115–143; whole-file SHA-256
`650281a7282f345ec940ffcf4b5e7b794a2e18c6e34838a4def9649fe89ac2d5`). Registered source:
`external-lean-reuse-snapshots-2026-10-21`, fingerprint
`26e8c647ade044fe9bd4dd1f9d997d4ca12aaa4766e55ab31cb64ca9f8415e01`. The source's two-step
`calc` of its theorem `finrank_finiteResidueGaloisIntermediateFieldIn` (M236.009, lines 104–110)
is also reused, inside the proof (see below).

## Target

Under the source's `variable` blocks (lines 39–41), the theorem takes, in order, `k : Type u`,
`[Field k]`, `[Fintype k]`, `Omega : Type v`, `[Field Omega]`, `[Algebra k Omega]`,
`[Algebra.IsAlgebraic k Omega]` and `[IsAlgClosed Omega]`, at arbitrary universes `u` and `v`.
Its type is `residueAbsoluteFrobenius_isAlgClosure_injectiveStatement k Omega`, which is

```lean
haveI : IsAlgClosure k Omega := ⟨inferInstance, inferInstance⟩
haveI : IsGalois k Omega := {}
Function.Injective (residueAbsoluteFrobenius k Omega)
```

That is, the canonical Frobenius homomorphism
`residueAbsoluteFrobenius k Omega : ZHatMul →ₜ* (Omega ≃ₐ[k] Omega)` (M168.005) on an algebraic
closure `Omega` of the finite field `k` is injective. The two `haveI`s supply the values of the
source's private instances M236.002 (`IsAlgClosure k Omega`) and M236.003 (`IsGalois k Omega`),
as explained in the Markdown of the target.

## Implemented proof

The proof first installs the same two instances with local `have`s, so that the instance
arguments of `residueAbsoluteFrobenius` agree with those in the target (both classes are
propositions, so any two instances agree). After
`show Function.Injective (residueAbsoluteFrobenius k Omega)`, it follows the source proof.

1. Take `z w : ZHatMul` with equal images. By `Multiplicative.ext` and the published
   extensionality theorem `Langlands.NYLL.ClassFormation.ZHat.ext` (the proof of
   `ZHat.extStatement`, module `ProfiniteIntegerCore/U021/Proofs`), it suffices to show
   `zHatReduction n hn z.toAdd = zHatReduction n hn w.toAdd` for every `n` with `hn : 0 < n`.
2. Fix such an `n` and let `E := finiteResidueGaloisIntermediateFieldIn k Omega n` (M236.008),
   the embedded degree-`n` finite Galois subextension. Apply `AlgEquiv.restrictNormalHom E` to
   the equality and rewrite both sides with the published M168.006 theorem
   `restrictNormalHom_residueAbsoluteFrobenius` (module `ResidueAbsoluteFrobenius/U006/Proofs`).
   This gives equality of the finite Frobenius coordinates
   `finiteResidueFrobeniusIntermediate k Omega E z` and `... w`. After the local instance
   `Finite E` (from `Module.finite_of_finite k`), `change` presents them as
   `finiteResidueFrobeniusFromZHat k E z` and `... w` (M167 data).
3. Rewrite with the published `finiteResidueFrobeniusFromZHat_apply` (M167.012, module
   `FiniteResidueFrobenius/U012/Proofs`), which expresses both sides through the finite exponent
   homomorphism applied to the reductions modulo `Module.finrank k E`. The published injectivity
   theorem `finiteResidueFrobeniusExponentHom_injective` (M167.007, module
   `FiniteResidueFrobenius/U007/Proofs`), followed by `Multiplicative.toAdd` and
   `simp only [toAdd_ofAdd]`, gives equality of the reductions of `z.toAdd` and `w.toAdd` modulo
   `Module.finrank k E`.
4. The degree `Module.finrank k E = n` is proved in place by the source's M236.009 argument:
   with a local `Fact (ringChar k).Prime` (from `CharP.char_is_prime`, the value of the source's
   private M236.001), a `calc` transports `Module.finrank` along the linear equivalence
   underlying `finiteResidueExtensionEquivIntermediateIn k Omega n` (M236.007) from
   `FiniteField.Extension k (ringChar k) n`, whose degree over `k` is `n` by Mathlib's
   `FiniteField.finrank_extension`. Hence `n ∣ Module.finrank k E`. Applying `ZMod.castHom` for
   this divisibility and rewriting with the published `zHatReduction_transition` (the proof of
   `zHatReduction_transitionStatement`, module `ProfiniteIntegerCore/U022/Proofs`) turns the
   equality modulo `Module.finrank k E` into the required equality modulo `n`.

Lean unfolds the published `Statement` types of `ZHat.ext`, `zHatReduction_transition` and
`restrictNormalHom_residueAbsoluteFrobenius` when they are applied or used for rewriting, so the
source tactic script needs no change there. No auxiliary declaration, instance or hypothesis is
added; the instances above are local to the proof. The theorem depends only on the axioms
`propext`, `Classical.choice` and `Quot.sound`.

## Modifications

- Namespace prefixed by `Langlands.NYLL`. The theorem's type is the published `Statement` rather
  than the restated proposition.
- The values of the private instances M236.002 and M236.003 come from local `have`s in the proof
  instead of the source's private section instances. M236.003 is built as `{}` from the local
  `IsAlgClosure` instance. The source's `infer_instance` would use Mathlib's
  `IsAlgClosure.isGalois`, which needs `CharZero` in the pinned Mathlib.
- A `show` step unfolds the target before the source script.
- The source's step `hdegree`, which applies its theorem
  `finrank_finiteResidueGaloisIntermediateFieldIn` (M236.009), is replaced by that theorem's own
  two-step `calc` (source lines 104–110) inside the proof, preceded by a local
  `Fact (ringChar k).Prime` standing for the private M236.001. No separate proof of M236.009 is
  imported, so this proof does not depend on the M236.009 proof task.
- Imports: the published modules `ResidueAlgebraicClosureDegree/Frobenius/Statements`,
  `ResidueAlgebraicClosureDegree/Initial/Definitions`, `ResidueAbsoluteFrobenius/U006/Proofs`
  (M168.006), `FiniteResidueFrobenius/U007/Proofs`, `FiniteResidueFrobenius/U012/Proofs` and
  `ProfiniteIntegerCore/U021/Proofs` and `U022/Proofs`, in place of the NYLL source imports. The
  `open` commands are those of the published Frobenius modules: the source's, without
  `RamificationTheory.Field.absoluteGaloisGroup` (unused), plus `ClassFormation` for the
  profinite-integer names.

The original copyright and author header is retained. Apache-2.0 attribution and notices are in
`licenses/NYLL/LICENSE` and `licenses/NYLL/NOTICE`. Environment
`5c94c648-e8dc-4002-a50a-071ebf3f6096` (Lean 4.34.0, Mathlib
`5ed2965256430c3649e86755f9576b54eca72435`).
