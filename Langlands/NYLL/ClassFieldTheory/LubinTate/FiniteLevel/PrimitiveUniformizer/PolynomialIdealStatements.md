# Polynomial evaluation in an ideal

This pair contributes only the proposition definition
`Langlands.NYLL.PortInternal.M346.d029Statement`. It states the exact
type of the private source helper M346.029
`LubinTate.polynomial_eval₂_mem_ideal_of_coeff_mem`: for independently
universe polymorphic commutative semirings `R` and `S`, a ring homomorphism
`f : R →+* S`, an ideal `I` of `S`, a polynomial `P` over `R` and `z : S`,
the explicit premise `hcoeff : ∀ i, f (P.coeff i) ∈ I` implies that
`P.eval₂ f z ∈ I`. No proof is contributed here.

The pinned source is Naganori Yamaguchi's ClassFieldTheory at commit
`fbd320cd8b1b06487c58227e92eb135794267709`,
`Nyll/ClassFieldTheory/LubinTate/FiniteLevel/PrimitiveUniformizer.lean`,
lines 494–498 for the type and 498–501 for its proof. The source file's
SHA-256 is
`71baf186fb2d8f7c934c51822144430966e5d6f7738a37fc52e7c8a4c42c5abc`.
It is contained in registered source
`external-lean-reuse-snapshots-2026-10-21`, content fingerprint
`26e8c647ade044fe9bd4dd1f9d997d4ca12aaa4766e55ab31cb64ca9f8415e01`.

The source's valuation calculation M346.031 applies this helper to the
nonleading part of the primitive division polynomial and its divided
polynomial. This is a prerequisite of the retained M346.033–.035 valuation
interface. A focused search of the current Library and pinned Mathlib found
no theorem with this complete mapped-coefficient hypothesis and evaluation
conclusion. Mathlib's `Polynomial.eval₂_eq_sum_range`, `Ideal.sum_mem` and
`Ideal.mul_mem_right` are the ingredients of the original short proof;
the exact proof of this target remains separate work.

Changes from the source are the public stable internal name, the namespace
prefix `Langlands.NYLL`, conversion from a private theorem to a `def`
returning `Prop`, removal of its proof, and replacement of the large
Lubin–Tate imports by the two Mathlib imports. The unused ambient field
section and namespace openings are omitted. They do not occur in the
helper's type. The two independent `Type*` parameters, all instance and
explicit arguments, the premise and the conclusion are retained. This
generic helper introduces no LocalField data, level field or instance.
The local unused-variable linter option allows the source name `hcoeff`
to remain even though its proof value is not used in the proposition body.

The Lean header preserves the original copyright, Apache-2.0 notice and
author attribution and records the dated extraction. The existing
[NYLL license](../../../../../../licenses/NYLL/LICENSE) and
[NYLL notice](../../../../../../licenses/NYLL/NOTICE) remain unchanged.
Supplementary attribution is registered as
`nyll-classfieldtheory-fbd320cd-supplement`, content fingerprint
`a81005c3aceabc51e9193cdc643d4dd81dd9d496dca2a0cf0111ce610d5b0330`.
