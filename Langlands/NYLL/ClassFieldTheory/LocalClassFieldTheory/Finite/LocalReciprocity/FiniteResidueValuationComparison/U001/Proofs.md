# Finite-separable comparison of restricted valuation rings: proof of M251.001

The theorem
`Langlands.NYLL.LocalClassFieldTheory.ValuationSubring.restrictIntermediateField_eq_of_finite_separable`
has exactly the closed published type
`Langlands.NYLL.LocalClassFieldTheory.ValuationSubring.restrictIntermediateField_eq_of_finite_separableStatement.{u, v, w}`.
Given a complete DVF `base` on `K`, an extension valuation subring `A` of an
arbitrary field extension `Omega / K`, a finite separable intermediate field
`E`, and any extension valuation subring `C` of `E`, it proves
`A.restrictIntermediateField E = C`. The field and value-group universes
remain independent (`u` for `K`, `v` for `Omega` and hence `E`, and `w` for
the base value group). No algebraicity assumption on `Omega` and no
residue-field, Galois or local-field hypothesis is introduced.

## Implemented proof and dependencies

First the separately proved M233.007 theorem
`Langlands.NYLL.RamificationTheory.ValuationSubring.restrictIntermediateField_hasExtension`
installs the extension instance for `A.restrictIntermediateField E`.
The published theorem
`Langlands.NYLL.ValuationTheory.DiscreteValuationField.ValuedExtension.exists_integralClosure_standard_completeDVF_extension`
then produces a complete-DVF structure `target` on `E`, together with a
valuation-extension witness and an `IsIntegralClosure` instance for its
valuation subring over the base valuation subring. These two instances are
installed locally. The existence theorem is instantiated at `.{u, w, v}`:
its second universe is the base value-group universe, while its third is
the extension-field universe. Its target value group lies in `Type 0`.

A local comparison `hcomp` shows that `target.valuation.valuationSubring`
equals every valuation subring `D` of `E` extending the base valuation:

1. `IsIntegralClosure.isIntegral_iff` makes every element of the target ring
   integral over the base valuation ring. `IsIntegral.tower_top` makes it
   integral over the valuation ring of `D.valuation`. The integrally closed
   ring-of-integers property
   `(Valuation.valuationSubring.integers D.valuation).mem_of_integral`
   places the element in that ring. This proves containment.
2. The comparison ring is proper. The base valuation is nontrivial, so
   `Valuation.IsNontrivial.exists_one_lt` supplies `a : K` of value greater
   than one. If the comparison ring were the whole field, its value on the
   image of `a` would be at most one. The extension equivalence
   `Valuation.HasExtension.val_map_le_one_iff` would imply that the base
   value of `a` is at most one, a contradiction.
3. Mathlib's `ValuationSubring.eq_of_le_of_ne_top` uses the rank-one property
   of the target's complete discrete valuation to turn this containment in
   a proper valuation overring into equality. The canonical valuation of a
   valuation subring recovers that subring, so simplification yields the
   equality with `D` itself.

Applying `hcomp` to the restriction and to `C`, then composing one equality
with the inverse of the other, proves the exact target.

The three direct imports are the published M251.001 `Statement` module,
the M233.007 `U007.Proofs` module, and
`Langlands.NYLL.ValuedFieldTheory.Valuation.DiscreteValuationField.FiniteIntegralClosure.StandardCompleteDVFExtensionProof`.
The latter provides the existence theorem and the required Mathlib
integral-closure and valuation-ring interfaces through its import closure.
The comparison argument follows the existing Library proof
`Langlands.NYLL.LocalFieldTheory.chosenLocalExtension_uniqueValuationExtension`
in `Langlands/NYLL/ValuedFieldTheory/LocalField/NonarchimedeanLocalField/FiniteExtensionCompleteDVF/ChosenUniquenessProof.lean`,
by Worker 1199, with `D.valuation` as the comparison valuation. That
local-field theorem is a proof-route reference, not an imported dependency.
Worker 122 supplied the compiled closed-target adaptation guidance.

## Source correspondence and replacement

The original is Naganori Yamaguchi's *ClassFieldTheory (NYLL)*, commit
`fbd320cd8b1b06487c58227e92eb135794267709`,
[`Nyll/ClassFieldTheory/LocalClassFieldTheory/Finite/LocalReciprocity/FiniteResidueValuationComparison.lean`, lines 33–59](https://github.com/n-yamaguchi-0729/ClassFieldTheory/blob/fbd320cd8b1b06487c58227e92eb135794267709/Nyll/ClassFieldTheory/LocalClassFieldTheory/Finite/LocalReciprocity/FiniteResidueValuationComparison.lean#L33-L59),
with namespace/universe context at lines 21–31. Worker 256 read the entire
62-line original, and also read the complete 344-line M233 source containing
the restriction-extension theorem. The M251 source file SHA-256 is
`3bccfb4b9d1259718ed253339c34d5d5e80b6266c627ad9d5cf90512a4633c90`.

The source first obtains the extension instance for the restricted ring
(lines 45–48), then invokes M245.018
`exists_integralClosure_standard_fundamental_identity` (49–51), compares both
rings through M196.039
`target_valuationSubring_eq_of_finite_separable` (53–58), and concludes by
transitivity (59). This proof keeps the restriction-extension and final
transitivity steps. It replaces M245.018 by its published existence,
HasExtension and actual-integral-closure consequence; the fundamental
identity is unnecessary here. M196.039 is not ported. Its two uses are
replaced by the local containment, properness and rank-one argument above.
No uniqueness assumption or unproved comparison theorem is added.

Other modifications introduce the closed statement telescope, prefix the
namespace by `Langlands.NYLL`, qualify Mathlib valuation names, name the base
value-group universe explicitly and replace the two upstream imports with
the three focused imports. The accepted statement and all published imports
are unchanged.

## Attribution

The registered originals are `external-lean-reuse-snapshots-2026-10-21`
(fingerprint `26e8c647ade044fe9bd4dd1f9d997d4ca12aaa4766e55ab31cb64ca9f8415e01`)
and `nyll-classfieldtheory-fbd320cd-supplement`
(fingerprint `a81005c3aceabc51e9193cdc643d4dd81dd9d496dca2a0cf0111ce610d5b0330`).
No matching source erratum was found. The original copyright and author
header are preserved; Apache-2.0 applies. The existing
[LICENSE](../../../../../../../../licenses/NYLL/LICENSE) and
[NOTICE](../../../../../../../../licenses/NYLL/NOTICE) are reused unchanged.
The Lean header records the modifications by Worker 256 on 13 November 2026;
Workers 122 and 1199 are credited for the proof guidance and reused comparison
argument. The approved check environment is
`5c94c648-e8dc-4002-a50a-071ebf3f6096` (Lean 4.34.0, Mathlib
`5ed2965256430c3649e86755f9576b54eca72435`). This is a valuation-ring support
proof; it asserts no host class-formation, cup, transfer, Tate or reciprocity
result.
