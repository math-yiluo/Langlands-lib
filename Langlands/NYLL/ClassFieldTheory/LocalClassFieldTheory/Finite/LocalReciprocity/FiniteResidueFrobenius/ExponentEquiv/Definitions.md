# Finite residue Frobenius coordinate equivalence

Adapted by Worker 123 from Naganori Yamaguchi, ClassFieldTheory (NYLL), pinned commit
`fbd320cd8b1b06487c58227e92eb135794267709`, source
`Nyll/ClassFieldTheory/LocalClassFieldTheory/Finite/LocalReciprocity/FiniteResidueFrobenius.lean`.
Registered source: `external-lean-reuse-snapshots-2026-10-21`, fingerprint
`26e8c647ade044fe9bd4dd1f9d997d4ca12aaa4766e55ab31cb64ca9f8415e01`. The source file is readable under
`/home/taskhub/pilot/literature/External Lean project reuse survey- pinned source snapshots, 21 October 2026/n-yamaguchi-0729--ClassFieldTheory/source`.

| Unit | Original declaration and source lines | Adapted declaration |
| --- | --- | --- |
| M167.008 | `finiteResidueFrobeniusExponentEquiv` (111–116) | `finiteResidueFrobeniusExponentEquiv` |

The original name is in `LocalClassFieldTheory`; the adapted name is in
`Langlands.NYLL.LocalClassFieldTheory`.

## Content

For a field `k : Type u` with `[Fintype k]` and a finite field `L : Type v`
(`[Finite L]`) with a `k`-algebra structure (source `variable` block, lines
36–37, retained verbatim),
`finiteResidueFrobeniusExponentEquiv k L :
Multiplicative (ZMod (Module.finrank k L)) ≃* (L ≃ₐ[k] L)` is the group
isomorphism `MulEquiv.ofBijective` built from the published M167.003
homomorphism `finiteResidueFrobeniusExponentHom k L`
(`ofAdd (m mod [L : k]) ↦ Frob^m`, with `Frob` the arithmetic Frobenius
`x ↦ x ^ #k`). Its bijectivity is supplied by the published proofs of M167.007
(`finiteResidueFrobeniusExponentHom_injective`) and M167.006
(`finiteResidueFrobeniusExponentHom_surjective`), whose types are the targets
`..._injectiveStatement k L` and `..._surjectiveStatement k L`, definitionally
`Function.Injective` and `Function.Surjective` of the homomorphism. Its
underlying function is therefore `finiteResidueFrobeniusExponentHom k L`.

## Modifications

- Namespace prefixed by `Langlands.NYLL`; the source `variable` block,
  universes `u v w`, `open ClassFormation`, the type, the body and the
  `noncomputable section` are retained. The definition uses every section
  binder, so its parameters are those of the source definition.
- The source module is replaced by imports of the published proof modules of
  M167.006 and M167.007 (`...FiniteResidueFrobenius.U006.Proofs`,
  `...FiniteResidueFrobenius.U007.Proofs`), which bring the M167.003 definition.
- The source `@[simp]` theorems after it (M167.009
  `finiteResidueFrobeniusExponentEquiv_apply`, line 120, and M167.010
  `finiteResidueFrobeniusExponentEquiv_one`, line 127) are outside Task 5860
  and not adapted.

The original copyright and author header is retained. Apache-2.0 attribution
and notices are in `licenses/NYLL/LICENSE` and `licenses/NYLL/NOTICE`.
This support unit makes no claim to discharge the host class-formation, cup,
transfer, Tate or reciprocity targets.
