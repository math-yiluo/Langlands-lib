# The Frobenius image is the whole Galois group (proof)

This module proves the published target
`Langlands.NYLL.LocalClassFieldTheory.residueAbsoluteFrobeniusRangeIn_eq_topStatement`
(M236.014, in `ResidueAlgebraicClosureDegree/Frobenius/Statements.lean`) by the theorem
`Langlands.NYLL.LocalClassFieldTheory.residueAbsoluteFrobeniusRangeIn_eq_top`.

Adapted by Worker 484 from Naganori Yamaguchi, ClassFieldTheory (NYLL), pinned commit
`fbd320cd8b1b06487c58227e92eb135794267709`, source
`Nyll/ClassFieldTheory/LocalClassFieldTheory/Finite/LocalReciprocity/ResidueAlgebraicClosureDegree.lean`,
theorem `residueAbsoluteFrobeniusRangeIn_eq_top`, lines 203–210 (whole-file SHA-256
`650281a7282f345ec940ffcf4b5e7b794a2e18c6e34838a4def9649fe89ac2d5`). Registered source:
`external-lean-reuse-snapshots-2026-10-21`. The theorem name and statement come from the source.
The proof script is new; it takes a different route, described below.

## Target

Under the source's `variable` blocks (lines 39–41), the theorem takes, in order, `k : Type u`,
`[Field k]`, `[Fintype k]`, `Omega : Type v`, `[Field Omega]`, `[Algebra k Omega]`,
`[Algebra.IsAlgebraic k Omega]` and `[IsAlgClosed Omega]`, at arbitrary universes `u` and `v`.
Its type is `residueAbsoluteFrobeniusRangeIn_eq_topStatement k Omega`, which is

```lean
(residueAbsoluteFrobeniusRangeIn k Omega).toSubgroup = ⊤
```

The closed subgroup `residueAbsoluteFrobeniusRangeIn k Omega` (M236.012) is the image of the
canonical Frobenius homomorphism `residueAbsoluteFrobenius k Omega : ZHatMul →ₜ* (Omega ≃ₐ[k] Omega)`.
The theorem says that this image is all of `Omega ≃ₐ[k] Omega`.

## Implemented proof

The proof uses the published M236.015 theorem
`Langlands.NYLL.LocalClassFieldTheory.residueAbsoluteFrobenius_isAlgClosure_surjective`
(module `ResidueAlgebraicClosureDegree/U015/Proofs`). It states that
`residueAbsoluteFrobenius k Omega` is surjective, with the `IsAlgClosure k Omega` and
`IsGalois k Omega` instances supplied by `haveI`s inside its target.

1. Unfold the M236.015 target in the hypothesis and the M236.014 target in the goal.
2. Rewrite the goal with `eq_top_iff`: the goal becomes `⊤ ≤ toSubgroup`. For each
   automorphism `sigma`, it must be shown that `sigma` lies in
   `(residueAbsoluteFrobeniusRangeIn k Omega).toSubgroup`.
3. By the M236.012 definition, this subgroup is
   `(residueAbsoluteFrobenius k Omega).toMonoidHom.range`. Membership in it means that `sigma`
   is the value of the Frobenius homomorphism at some element. Surjectivity gives exactly
   that element, so `exact hsurj sigma` closes the goal by definitional unfolding.

The instances inside the M236.012 definition and inside the M236.015 target are both built as
`⟨inferInstance, inferInstance⟩` and `{}`. They are proofs of the propositions
`IsAlgClosure k Omega` and `IsGalois k Omega`, so the two Frobenius homomorphisms agree
definitionally. No auxiliary declaration, instance or hypothesis is added. `lean_check` reports
only the axioms `propext`, `Classical.choice` and `Quot.sound`.

## Modifications

- Namespace prefixed by `Langlands.NYLL`. The theorem's type is the published `Statement`
  rather than the restated proposition.
- Different proof route. The source proof script (lines 206–210) applies Mathlib's
  `InfiniteGalois.fixingSubgroup_fixedField` to the closed image. It then rewrites with the
  source theorem M236.013 `fixedField_residueAbsoluteFrobeniusRangeIn` (the fixed field is `⊥`)
  and with `IntermediateField.fixingSubgroup_bot`. The proof of M236.013 (Task 6930) is not in
  the Library. So this proof instead derives the result from the published M236.015
  surjectivity theorem: the image of a surjective homomorphism is the whole group. In the
  source, M236.015 is proved from M236.014. The published M236.015 proof does not import
  M236.014. It proves M236.013 and M236.014 locally, by the source's infinite-Galois argument.
  Hence there is no circularity.
- No private instance is declared. The source's private instances M236.002 (`IsAlgClosure`)
  and M236.003 (`IsGalois`) are not needed as hypotheses here. Their values enter only through
  the published M236.012 definition and the M236.015 target, which supply them by `haveI`.
- Imports: the published target module `ResidueAlgebraicClosureDegree/Frobenius/Statements` and
  the published proof module `ResidueAlgebraicClosureDegree/U015/Proofs`, in place of the NYLL
  source imports. The `open` commands are those of the published Frobenius modules: the source's,
  without `RamificationTheory.Field.absoluteGaloisGroup` (unused), plus `ClassFormation` for the
  profinite-integer names.

The original copyright and author header is retained. Apache-2.0 attribution and notices are in
`licenses/NYLL/LICENSE` and `licenses/NYLL/NOTICE`. Environment
`5c94c648-e8dc-4002-a50a-071ebf3f6096` (Lean 4.34.0, Mathlib
`5ed2965256430c3649e86755f9576b54eca72435`).
