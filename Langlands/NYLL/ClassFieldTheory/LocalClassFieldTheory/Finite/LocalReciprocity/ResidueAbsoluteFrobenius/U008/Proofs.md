# M168.008: `restrictNormalHom_frobeniusAlgEquivOfAlgebraic` (proof)

Proves the published target
`Langlands.NYLL.LocalClassFieldTheory.restrictNormalHom_frobeniusAlgEquivOfAlgebraicStatement` as
`theorem Langlands.NYLL.LocalClassFieldTheory.restrictNormalHom_frobeniusAlgEquivOfAlgebraic`.
The theorem is stated under the source's `variable` block
`(k : Type u) (Omega : Type v) [Field k] [Fintype k] [Field Omega] [Algebra k Omega]
[IsGalois k Omega]` with the explicit argument `(E : FiniteGaloisIntermediateField k Omega)`,
and its type is the target applied to these parameters in this order, which is the target's own
binder order.

Mathematically: for a finite field `k` and an algebraic Galois extension `Omega` of `k`, the
restriction `AlgEquiv.restrictNormalHom E` to a finite Galois intermediate field `E` sends the
arithmetic Frobenius `x ↦ x ^ #k` of `Omega` (`FiniteField.frobeniusAlgEquivOfAlgebraic k Omega`)
to the arithmetic Frobenius of `E` (`FiniteField.frobeniusAlgEquivOfAlgebraic k E`).

Adapted from Naganori Yamaguchi, ClassFieldTheory (NYLL), pinned commit
`fbd320cd8b1b06487c58227e92eb135794267709`, source
`Nyll/ClassFieldTheory/LocalClassFieldTheory/Finite/LocalReciprocity/ResidueAbsoluteFrobenius.lean`,
lines 138–159. Registered source `external-lean-reuse-snapshots-2026-10-21`, fingerprint
`26e8c647ade044fe9bd4dd1f9d997d4ca12aaa4766e55ab31cb64ca9f8415e01`.

## Proof

The source proof script, unchanged. The target is a `def` whose body is an equation of
`k`-algebra automorphisms of `E`; `apply AlgEquiv.ext` unfolds it and reduces it to pointwise
equality at every `x : E`. Since `algebraMap E Omega` is injective, it suffices to compare the
images of both sides in `Omega`:

1. `AlgEquiv.restrictNormal_commutes` identifies the image of the restricted Frobenius applied
   to `x` with Frobenius of `Omega` applied to `algebraMap E Omega x`.
2. Rewriting both Frobenius maps with `FiniteField.coe_frobeniusAlgEquivOfAlgebraic` (each is
   `· ^ Fintype.card k`), the remaining equation
   `(algebraMap E Omega x) ^ Fintype.card k = algebraMap E Omega (x ^ Fintype.card k)`
   is `map_pow` for the ring homomorphism `algebraMap E Omega`.

The proof uses only Mathlib declarations; it introduces no axiom, instance or auxiliary
declaration.

## Imports and modifications

Imports: the target module
`Langlands.NYLL.ClassFieldTheory.LocalClassFieldTheory.Finite.LocalReciprocity.ResidueAbsoluteFrobenius.Initial.Statements`,
which is unchanged. The namespace is prefixed by `Langlands.NYLL`. The theorem's stated type is
the `Statement` target instead of the source proposition; the target's body is that proposition
verbatim, so the two are definitionally equal. The source universes, `open` commands and
`noncomputable section` are retained.

The original copyright and author header is retained, followed by a modification notice. Apache-2.0
attribution and notices are in `licenses/NYLL/LICENSE` and `licenses/NYLL/NOTICE`.
