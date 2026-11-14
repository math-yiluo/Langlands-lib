# Proof of polynomial evaluation in an ideal

This pair proves the imported proposition
`Langlands.NYLL.PortInternal.M346.d029Statement` with the theorem
`Langlands.NYLL.PortInternal.M346.d029`. Its conclusion is the fully
applied target `d029Statement f I P z hcoeff`. The telescope retains
independent universes for the commutative semirings `R` and `S`, both
instances, the ring homomorphism `f : R →+* S`, ideal `I : Ideal S`,
polynomial `P : Polynomial R`, evaluation point `z : S`, and the explicit
premise `hcoeff : ∀ i, f (P.coeff i) ∈ I`. No additional hypothesis is used.
The published statement pair and its imports are unchanged.

The proof first exposes the target's definition, whose conclusion is
`P.eval₂ f z ∈ I`. It rewrites the evaluation with
`Polynomial.eval₂_eq_sum_range` as the finite sum of
`f (P.coeff i) * z ^ i` for `i` in `Finset.range (P.natDegree + 1)`.
For each summand, `Ideal.mul_mem_right (z ^ i) I (hcoeff i)` proves
membership in `I`. Then the inherited `Submodule.sum_mem`, invoked as
`I.sum_mem`, proves membership of the sum.
The proof additionally imports `Mathlib.Algebra.Polynomial.Eval.Degree`
for the finite-sum identity.

The source is Naganori Yamaguchi's ClassFieldTheory, pinned at commit
`fbd320cd8b1b06487c58227e92eb135794267709`,
`Nyll/ClassFieldTheory/LubinTate/FiniteLevel/PrimitiveUniformizer.lean`,
lines 494–501, private theorem
`LubinTate.polynomial_eval₂_mem_ideal_of_coeff_mem` (inventory M346.029).
The type occurs at lines 494–498 and the implemented finite-sum proof at
lines 498–501. The source file's SHA-256 is
`71baf186fb2d8f7c934c51822144430966e5d6f7738a37fc52e7c8a4c42c5abc`.
It is in registered source `external-lean-reuse-snapshots-2026-10-21`,
content fingerprint
`26e8c647ade044fe9bd4dd1f9d997d4ca12aaa4766e55ab31cb64ca9f8415e01`.

The finite-sum proof is retained from the source. Changes are its public
internal name and qualified namespace, explicit names for the two independent
universes, a conclusion naming the imported Prop target, the initial `change`
that exposes that target, use of `I.sum_mem` in place of the unavailable
`Ideal.sum_mem` name in the pinned Mathlib, and reduced imports. The source's unused ambient
Lubin–Tate field context is omitted; it supplies no parameter or premise
to this generic semiring theorem. No local helper is added.

The Lean header preserves the source copyright, Apache-2.0 notice and
author attribution and records the dated modifications by Worker 669.
The existing [NYLL license](../../../../../../licenses/NYLL/LICENSE) and
[NYLL notice](../../../../../../licenses/NYLL/NOTICE) remain unchanged.
Supplementary attribution is registered as
`nyll-classfieldtheory-fbd320cd-supplement`, content fingerprint
`a81005c3aceabc51e9193cdc643d4dd81dd9d496dca2a0cf0111ce610d5b0330`.
