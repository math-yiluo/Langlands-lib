# NYLL M329.002: trivial upper ramification for an unramified extension

The theorem
`Langlands.NYLL.RamificationTheory.LocalField.localUpperRamificationGroup_eq_bot_of_unramifiedValuation`
has exactly the published closed proposition type
`Langlands.NYLL.RamificationTheory.LocalField.localUpperRamificationGroup_eq_bot_of_unramifiedValuationStatement`.
It proves that every real nonnegative-index upper ramification group of the
actual finite unramified Galois extension is bottom. The target's fields are
`K L : Type`, with the source's two nonarchimedean local-field structures,
finite-dimensional Galois algebra, supplied valuation extension, integral-closure
and integer-module finiteness instances, and the published
`IsNonarchimedeanLocalField.IsUnramifiedValuedExtension K L` class. The target is
imported from `Unramified.Statement`; its Lean and Markdown pair is unchanged.

## Implemented proof and published inputs

For `t ≥ 0`, lower-group antitonicity and the monotonicity of the inverse
Herbrand function give `localUpperRamificationGroup K L t ≤
localUpperRamificationGroup K L 0`. This comparison directly uses the published
`Higher.lowerRamificationGroup_antitone` and
`Higher.inverseHerbrandFunctionOfUniqueExtension_strictMono`, rather than
requiring a separately unpublished local antitonicity theorem. It installs only
the local witness `Classical.choose (chosenLocalExtension_properties K L)` and
uses `chosenLocalExtension_uniqueValuationExtension.{0} K L`. Thus it uses exactly
the chosen-extension convention of the published actual upper groups and adds
no global instance.

The published
`Langlands.NYLL.RamificationTheory.LocalField.localUpperRamificationGroup_zero_eq_residue_ker`
(M328.002, `LocalField.ResidueInertia.Proofs`) identifies the group at zero
with the kernel of the supplied residue-action homomorphism.
The first component of the already published theorem
`Langlands.NYLL.LocalFieldTheory.galoisGroupResidueAlgEquivHomOfIsIntegralClosure_bijective_of_unramifiedValuation`
(M161.035, `FiniteUnramified.ResidueBijectiveProof`) is its injectivity under the
exact hypotheses here, specialized to universe zero. Mathlib's
`MonoidHom.ker_eq_bot_iff` therefore makes that kernel bottom. Antisymmetry with
`bot_le` concludes.

This route needs no separate port of the source's private M329.001 lower-zero
helper or its M161.033 injectivity theorem: the published upper-zero identity
and bijectivity theorem supply their needed consequences by name. It does not
use the quotient theorem M326 or the separate M327.010 proof draft.

The focused imports are the published target, `LocalField.ResidueInertia.Proofs`,
`FiniteUnramified.ResidueBijectiveProof`, and
`HilbertRamification.HerbrandFunction.LawsProof`. All mathematical inputs are
published Library or Mathlib declarations.

## Source correspondence and modifications

Original: Naganori Yamaguchi, *ClassFieldTheory*, pinned commit
`fbd320cd8b1b06487c58227e92eb135794267709`,
`Nyll/ValuedFieldTheory/Ramification/LocalField/Unramified.lean`,
M329.002, signature lines 55–68 and proof lines 68–79. The whole-file SHA-256 is
`81d609ee80761316740480f408d238ad59883f4790d713337fcb195c5d3f7717`.

Worker 296 prefixed the namespace with `Langlands.NYLL`, proved the already
published closed target instead of restating its parameters externally, and
replaced whole-source imports by the focused published modules above. The
source proof passes from upper zero to lower zero and uses its private helper;
the implemented proof passes directly to the residue kernel using M328.002.
The source injectivity helper is replaced by the injectivity component of the
stronger published M161.035 theorem. The local antitone comparison is expanded
using the published generic lower and inverse-Herbrand results, with a local
chosen-extension witness. The source universes, hypotheses, actual upper-group
data and nonnegative-index conclusion remain exactly those of the target.

## Provenance and validation boundary

Registered source `external-lean-reuse-snapshots-2026-10-21`, content fingerprint
`26e8c647ade044fe9bd4dd1f9d997d4ca12aaa4766e55ab31cb64ca9f8415e01`;
attribution supplement `nyll-classfieldtheory-fbd320cd-supplement`, fingerprint
`a81005c3aceabc51e9193cdc643d4dd81dd9d496dca2a0cf0111ce610d5b0330`.
The original copyright and author header is retained and the changes are
recorded in the Lean header. The existing `licenses/NYLL/LICENSE` and
`licenses/NYLL/NOTICE` are unchanged (SHA-256 respectively
`b40930bbcf80744c86c46a12bc9da056641d722716c378f5659b9e555ef833e1`
and `bf19eab77be48af60691e32428ed2126785de7d36f975d06f286d28d80f71e22`).
No NYLL-specific erratum was found in the Library errata filenames.

The environment is `5c94c648-e8dc-4002-a50a-071ebf3f6096`, Lean 4.34.0 with
Mathlib `5ed2965256430c3649e86755f9576b54eca72435`. A development compilation
and declaration inspection are separate from the required independent semantic
review, exact-target proof validation and Library integration.

Development check `65b07a62-1cc2-422e-8cde-e003cca38b1e` compiled this module
with zero errors and warnings. Declaration inspection reported kind `theorem`,
no universe parameters, and only `propext`, `Classical.choice`, `Quot.sound`.
The Lean signature is the published Statement definition itself. This is
unreviewed development evidence; the child proof task must obtain exact-target
validation and independent acceptance.
