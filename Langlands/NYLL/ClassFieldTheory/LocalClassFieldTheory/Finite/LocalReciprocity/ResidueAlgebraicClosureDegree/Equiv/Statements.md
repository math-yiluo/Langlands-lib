# Finite coordinates of the intrinsic residue degree (target)

Adapted by Worker 46 from Naganori Yamaguchi, ClassFieldTheory (NYLL), pinned commit
`fbd320cd8b1b06487c58227e92eb135794267709`, source
`Nyll/ClassFieldTheory/LocalClassFieldTheory/Finite/LocalReciprocity/ResidueAlgebraicClosureDegree.lean`
(whole-file SHA-256 `650281a7282f345ec940ffcf4b5e7b794a2e18c6e34838a4def9649fe89ac2d5`).
Registered source: `external-lean-reuse-snapshots-2026-10-21`, fingerprint
`26e8c647ade044fe9bd4dd1f9d997d4ca12aaa4766e55ab31cb64ca9f8415e01`. The source file is readable under
`/home/taskhub/pilot/literature/External Lean project reuse survey- pinned source snapshots, 21 October 2026/n-yamaguchi-0729--ClassFieldTheory/source`.

| Unit | Original declaration and source lines | Adapted declaration |
| --- | --- | --- |
| M236.022 | `finiteResidueFrobeniusExponentEquiv_symm_restrict_in` (514–533) | `finiteResidueFrobeniusExponentEquiv_symm_restrict_inStatement` |

Every unqualified original name above is in `LocalClassFieldTheory`. Every adapted name is in
`Langlands.NYLL.LocalClassFieldTheory` unless fully qualified.

## Content

Let `k : Type u` be a field with `[Fintype k]`, and let `Omega : Type v` be a `k`-algebra field
with `[Algebra.IsAlgebraic k Omega]` and `[IsAlgClosed Omega]`, i.e. an algebraic closure of the
finite field `k`. Let `residueAbsoluteDegreeIn k Omega : (Omega ≃ₐ[k] Omega) →ₜ* ZHatMul` be the
intrinsic residue degree (M236.017), the inverse of the Frobenius equivalence
`ZHatMul ≃ₜ* (Omega ≃ₐ[k] Omega)`.

M236.022 (`finiteResidueFrobeniusExponentEquiv_symm_restrict_inStatement k Omega sigma E`). For an
automorphism `sigma : Omega ≃ₐ[k] Omega` and a finite Galois intermediate field
`E : FiniteGaloisIntermediateField k Omega`, with the local instance `Finite E` given by
`Module.finite_of_finite k`:

    (finiteResidueFrobeniusExponentEquiv k E).symm (AlgEquiv.restrictNormalHom E sigma)
      = Multiplicative.ofAdd
          (zHatReduction (Module.finrank k E) Module.finrank_pos
            (residueAbsoluteDegreeIn k Omega sigma).toAdd)

Here `finiteResidueFrobeniusExponentEquiv k E : Multiplicative (ZMod [E : k]) ≃* (E ≃ₐ[k] E)` is
the finite-level Frobenius coordinate equivalence (M167.008), `AlgEquiv.restrictNormalHom E sigma`
is the restriction of `sigma` to `E`, and `zHatReduction n hn : ContinuousAddMonoidHom ZHat (ZMod n)` is the
canonical reduction modulo `n` (with `hn : 0 < n`; here `n = [E : k]` and `hn` is `Module.finrank_pos`). In words: the
Frobenius exponent of `sigma` restricted to `E` is the residue degree of `sigma` reduced modulo
`[E : k]`.

Parameters, in order: `k`, `[Field k]`, `[Fintype k]`, `Omega`, `[Field Omega]`,
`[Algebra k Omega]`, `[Algebra.IsAlgebraic k Omega]`, `[IsAlgClosed Omega]`, `sigma`, `E`. The
source theorem has no `omit`, so it takes the full section telescope followed by its own arguments
`sigma` and `E`. Every section binder is used through `residueAbsoluteDegreeIn`.

## Modifications

- The namespace is prefixed by `Langlands.NYLL`. The source theorem is replaced by a Prop-valued
  definition with the `Statement` suffix. Its arguments `sigma` and `E` become explicit arguments
  of the definition, and its body is the source proposition, including the source's
  `letI : Finite E := Module.finite_of_finite k`. It sits under the source's `variable` blocks
  (lines 39–41) with the source's universes and `open` commands, except the dropped NYLL
  `open RamificationTheory.Field.absoluteGaloisGroup`, which is unused here. The source proof is
  omitted, so nothing is proved here.
- Private instances M236.001–M236.004 are not needed by the proposition: `IsGalois k Omega`,
  `IsAlgClosure k Omega` and the Hausdorff property enter only through `residueAbsoluteDegreeIn`,
  which inlines its own instances. `AlgEquiv.restrictNormalHom E` uses the `Normal k E` instance of
  a finite Galois intermediate field.
- Imports: the source imports of NYLL modules are replaced by the `Langlands.NYLL` modules
  `ResidueAlgebraicClosureDegree.Equiv.Definitions` (M236.016/.017) and
  `FiniteResidueFrobenius.ExponentEquiv.Definitions` (M167.008). `zHatReduction` is
  `Langlands.NYLL.ClassFormation.zHatReduction`.

The original copyright and author header is retained. Apache-2.0 attribution and notices are in
`licenses/NYLL/LICENSE` and `licenses/NYLL/NOTICE`. This support unit makes no claim to discharge
the host class-formation, cup, transfer, Tate or reciprocity targets.
