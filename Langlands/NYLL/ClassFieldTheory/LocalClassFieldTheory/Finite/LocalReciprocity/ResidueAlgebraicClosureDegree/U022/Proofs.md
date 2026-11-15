# Finite coordinates of the intrinsic residue degree (proof)

This module proves the published target
`Langlands.NYLL.LocalClassFieldTheory.finiteResidueFrobeniusExponentEquiv_symm_restrict_inStatement`
(M236.022, in `ResidueAlgebraicClosureDegree/Equiv/Statements.lean`) by the theorem
`Langlands.NYLL.LocalClassFieldTheory.finiteResidueFrobeniusExponentEquiv_symm_restrict_in`.

Adapted by Worker 46 (draft proof pair) and Worker 122 (check against the current Library and
Markdown corrections) from Naganori Yamaguchi, ClassFieldTheory (NYLL), pinned commit
`fbd320cd8b1b06487c58227e92eb135794267709`, source
`Nyll/ClassFieldTheory/LocalClassFieldTheory/Finite/LocalReciprocity/ResidueAlgebraicClosureDegree.lean`,
theorem `finiteResidueFrobeniusExponentEquiv_symm_restrict_in`, lines 514–532 (doc comment through
the last proof line; the task's locator 514–533 also covers the following blank line; whole-file SHA-256
`650281a7282f345ec940ffcf4b5e7b794a2e18c6e34838a4def9649fe89ac2d5`). Registered source:
`external-lean-reuse-snapshots-2026-10-21`, fingerprint
`26e8c647ade044fe9bd4dd1f9d997d4ca12aaa4766e55ab31cb64ca9f8415e01`.

## Target

Under the source's `variable` blocks (lines 39–41), the theorem takes, in order, `k : Type u`,
`[Field k]`, `[Fintype k]`, `Omega : Type v`, `[Field Omega]`, `[Algebra k Omega]`,
`[Algebra.IsAlgebraic k Omega]`, `[IsAlgClosed Omega]`, then
`sigma : Omega ≃ₐ[k] Omega` and `E : FiniteGaloisIntermediateField k Omega`. Its type is
`finiteResidueFrobeniusExponentEquiv_symm_restrict_inStatement k Omega sigma E`, which is

```lean
letI : Finite E := Module.finite_of_finite k
(finiteResidueFrobeniusExponentEquiv k E).symm
    (AlgEquiv.restrictNormalHom E sigma) =
  Multiplicative.ofAdd
    (zHatReduction (Module.finrank k E) Module.finrank_pos
      (residueAbsoluteDegreeIn k Omega sigma).toAdd)
```

The finite Frobenius coordinate (M167.008) of the restriction of `sigma` to `E` is the intrinsic
residue degree of `sigma` (M236.017) reduced modulo `[E : k]`.

## Implemented proof

The proof first installs local instances with `have : IsAlgClosure k Omega` and
`have : IsGalois k Omega := {}`, the values of the source's private instances M236.002 and
M236.003 (see the Markdown of `Equiv/Definitions`). They are needed to state the published M168.006
theorem used below, whose section requires `[IsGalois k Omega]`. It then sets
`let : Finite E := Module.finite_of_finite k` and unfolds the target with `show`. After that it is
the source proof:

1. Apply injectivity of `finiteResidueFrobeniusExponentEquiv k E` and cancel `symm` with
   `MulEquiv.apply_symm_apply`. The goal becomes
   `AlgEquiv.restrictNormalHom E sigma = finiteResidueFrobeniusExponentEquiv k E (… reduction …)`.
2. `finiteResidueFrobeniusExponentEquiv k E` (M167.008) is `MulEquiv.ofBijective` of
   `finiteResidueFrobeniusExponentHom k E` (M167.003), and `finiteResidueFrobeniusIntermediate k Omega E`
   (M168.001) is `finiteResidueFrobeniusFromZHat k E` (M167.011), which sends `z` to that
   homomorphism applied to the reduction of `z.toAdd` modulo `[E : k]`. So the right side is by
   definition
   `finiteResidueFrobeniusIntermediate k Omega E (residueAbsoluteDegreeIn k Omega sigma)`, and
   `change` restates the goal this way.
3. Rewrite right to left with the published M168.006 theorem
   `restrictNormalHom_residueAbsoluteFrobenius` (module `ResidueAbsoluteFrobenius/U006/Proofs`):
   the right side becomes `AlgEquiv.restrictNormalHom E (residueAbsoluteFrobenius k Omega
   (residueAbsoluteDegreeIn k Omega sigma))`, where `residueAbsoluteFrobenius` is M168.005.
4. `congr 1` reduces the goal to
   `sigma = residueAbsoluteFrobenius k Omega (residueAbsoluteDegreeIn k Omega sigma)`. Since
   `residueAbsoluteDegreeIn` is the inverse of `residueAbsoluteFrobeniusEquivIn` (M236.016), whose
   forward map is `residueAbsoluteFrobenius`, this is
   `(residueAbsoluteFrobeniusEquivIn k Omega).apply_symm_apply sigma` read backwards.

No auxiliary declaration, global instance or hypothesis is added; the three instances above are local to the proof.

## Modifications

- Namespace prefixed by `Langlands.NYLL`. The theorem's type is the published `Statement` rather
  than the restated proposition.
- The source relies on its private section instances for `IsGalois k Omega`. Here local `have`s
  supply the values. M236.003 is built as `{}` from the local `IsAlgClosure` instance, because the
  source's `infer_instance` would use Mathlib's `IsAlgClosure.isGalois`, which needs `CharZero` in
  the pinned Mathlib.
- A `show` step unfolds the target before the source script.
- Imports: the published modules `ResidueAlgebraicClosureDegree/Equiv/Statements` and
  `ResidueAbsoluteFrobenius/U006/Proofs`, in place of the NYLL source imports. The `open` commands
  are the source's (lines 26 and 34–37), without `open RamificationTheory.Field.absoluteGaloisGroup`,
  which the proof does not use; they are the same as in the published `Equiv/Statements` module.

The original copyright and author header is retained. Apache-2.0 attribution and notices are in
`licenses/NYLL/LICENSE` and `licenses/NYLL/NOTICE`. Environment
`5c94c648-e8dc-4002-a50a-071ebf3f6096` (Lean 4.34.0, Mathlib
`5ed2965256430c3649e86755f9576b54eca72435`).
