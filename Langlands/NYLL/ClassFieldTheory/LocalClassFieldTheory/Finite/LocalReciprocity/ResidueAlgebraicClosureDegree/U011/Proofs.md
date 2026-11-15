# Frobenius-fixed points of an algebraic closure of a finite field (proof)

This module proves the published target
`Langlands.NYLL.LocalClassFieldTheory.mem_range_algebraMap_iff_frobenius_fixed_inStatement`
(M236.011, in `ResidueAlgebraicClosureDegree/Initial/Statements.lean`) by the theorem
`Langlands.NYLL.LocalClassFieldTheory.mem_range_algebraMap_iff_frobenius_fixed_in`.

Adapted by Worker 46 from Naganori Yamaguchi, ClassFieldTheory (NYLL), pinned commit
`fbd320cd8b1b06487c58227e92eb135794267709`, source
`Nyll/ClassFieldTheory/LocalClassFieldTheory/Finite/LocalReciprocity/ResidueAlgebraicClosureDegree.lean`,
lines 145–170 (whole-file SHA-256
`650281a7282f345ec940ffcf4b5e7b794a2e18c6e34838a4def9649fe89ac2d5`). Registered source:
`external-lean-reuse-snapshots-2026-10-21`, fingerprint
`26e8c647ade044fe9bd4dd1f9d997d4ca12aaa4766e55ab31cb64ca9f8415e01`.

## Target

Under the source's `variable` blocks (lines 39–41) and its `omit [IsAlgClosed Omega]`, the
theorem takes, in order, `k : Type u`, `[Field k]`, `[Fintype k]`, `Omega : Type v`,
`[Field Omega]`, `[Algebra k Omega]`, `[Algebra.IsAlgebraic k Omega]` and `x : Omega`, and its type
is `mem_range_algebraMap_iff_frobenius_fixed_inStatement k Omega x`, which unfolds to

```lean
x ∈ Set.range (algebraMap k Omega) ↔
  FiniteField.frobeniusAlgEquivOfAlgebraic k Omega x = x
```

That is, for an algebraic field extension `Omega` of a finite field `k`, an element of `Omega`
comes from `k` exactly when the arithmetic Frobenius `y ↦ y ^ #k` fixes it. Algebraic closedness
is not assumed.

## Implemented proof

After `unfold mem_range_algebraMap_iff_frobenius_fixed_inStatement`, this is the source proof.

- Forward: for `x = algebraMap k Omega a`, `FiniteField.coe_frobeniusAlgEquivOfAlgebraic` rewrites
  Frobenius to the power `· ^ Fintype.card k`. Then `← map_pow` and `FiniteField.pow_card`
  (`a ^ #k = a` in `k`) close the goal.
- Backward: from the fixed-point hypothesis, `x ^ Fintype.card k = x`. So `x` is a root in `Omega`
  of `p = X ^ #k - X : k[X]`, which is nonzero by `FiniteField.X_pow_card_sub_X_ne_zero` (using
  `Fintype.one_lt_card`). Here `Polynomial.mem_rootSet_of_ne` and `simp` show
  `x ∈ p.rootSet Omega`. Since `k` is a splitting field of `p` over itself
  (`FiniteField.isSplittingField_sub k k`), the polynomial `p.map (algebraMap k k)` splits. By
  `Polynomial.Splits.image_rootSet` along `Algebra.ofId k Omega`, the roots of `p` in `Omega` are
  the images of its roots in `k`. Hence `x = algebraMap k Omega a` for some `a : k`.

No auxiliary declaration, instance or hypothesis is added.

## Modifications

- Namespace prefixed by `Langlands.NYLL`. The theorem's type is the published `Statement`, so the
  proof starts with `unfold` of that definition. The rest is the source proof verbatim.
- Imports: the published `ResidueAlgebraicClosureDegree/Initial/Statements` module, which is left
  unchanged, in place of the NYLL source imports. The `open` commands are those of the Initial
  modules. The source's `open ClassFormation` and
  `open RamificationTheory.Field.absoluteGaloisGroup` are dropped because this proof uses
  neither. The source's other declarations, including its private instance
  `finiteResidueBaseRingCharPrime` (lines 43–45), are not copied because this proof does not
  need them.

The original copyright and author header is retained. Apache-2.0 attribution and notices are in
`licenses/NYLL/LICENSE` and `licenses/NYLL/NOTICE`. Environment
`5c94c648-e8dc-4002-a50a-071ebf3f6096` (Lean 4.34.0, Mathlib
`5ed2965256430c3649e86755f9576b54eca72435`).
