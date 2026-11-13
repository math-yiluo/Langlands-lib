# NYLL M025: natural-multiple images and value-group reduction data

This file adapts five data definitions from Naganori Yamaguchi,
`Nyll/ClassFieldTheory/AbstractClassFieldTheory/Degree/Valuation.lean`,
commit `fbd320cd8b1b06487c58227e92eb135794267709`. The pinned source file has
SHA-256 `f630b84345567adaa22a76feb4a0c2716079721e29a7d3b12bf5c6bd52cabb0c`.
It is retained under
`/home/taskhub/pilot/literature/External Lean project reuse survey- pinned source snapshots, 21 October 2026/n-yamaguchi-0729--ClassFieldTheory/source/`.
The registered collection is `external-lean-reuse-snapshots-2026-10-21`,
fingerprint `26e8c647ade044fe9bd4dd1f9d997d4ca12aaa4766e55ab31cb64ca9f8415e01`.
The supplemental source registration is `nyll-classfieldtheory-fbd320cd-supplement`,
fingerprint `a81005c3aceabc51e9193cdc643d4dd81dd9d496dca2a0cf0111ce610d5b0330`.

All adapted names in this table have prefix `Langlands.NYLL.ClassFormation`;
all original names have prefix `ClassFormation`.

| Unit | Source declaration and exact lines | Adapted declaration |
| --- | --- | --- |
| M025.002 | `nsmulOnAddSubgroup`, 43–46 | `nsmulOnAddSubgroup` |
| M025.003 | `nsmulWithin`, 49–50 | `nsmulWithin` |
| M025.004 | `nsmulImage`, 53–57 | `nsmulImage` |
| M025.007 | `valueGroupReduction`, 80–82 | `valueGroupReduction` |
| M025.008 | `canonicalValueQuotientMap`, 89–95 | `canonicalValueQuotientMap` |

For an additive subgroup `Z` of the published NYLL closure model
`Langlands.NYLL.ClassFormation.ZHat : Type 0` and any natural number `n`,
`nsmulOnAddSubgroup Z n : Z →+ Z` sends a subgroup element to its natural
multiple, with its membership witnessed by `Z.nsmul_mem`. Its zero and
addition fields are exactly the source's subtype-extensionality proofs.
`nsmulWithin Z n : AddSubgroup Z` is this endomorphism's range, whereas
`nsmulImage Z n : AddSubgroup ZHat` is the ambient image of `Z` under the
explicit additive homomorphism `z ↦ n • z`. The two subgroups have different
ambient types, as in the source. These three definitions allow `n = 0`.

For explicit arguments `(Z : AddSubgroup ZHat) (n : ℕ) (hn : 0 < n)`,
`valueGroupReduction Z n hn : Z →+ ZMod n` composes the subgroup inclusion
with `(zHatReduction n hn).toAddMonoidHom`. The latter is the published
closure-coordinate reduction from
`Langlands.NYLL.GaloisCohomology.ProfiniteIntegers.ProfiniteIntegerCore.Definitions`.
This reuses the actual M008.008 and M008.018 constructions, without substituting
a different profinite-integer model or reduction.

`canonicalValueQuotientMap Z n hn : (Z ⧸ nsmulWithin Z n) →+ ZMod n`
is the specific `QuotientAddGroup.lift` of `valueGroupReduction Z n hn`.
Its proof that the subgroup is in the kernel is retained verbatim: write an
element of the range as a natural multiple, use `map_nsmul`, and simplify the
natural multiple in `ZMod n` with `nsmul_eq_mul`. No bijectivity is assumed or
proved. In particular this construction does not replace the induced map by
an arbitrarily selected quotient equivalence.

Worker 192 made the following modifications. The source namespace
`ClassFormation` is prefixed by `Langlands.NYLL`. Only the five listed data
commands are extracted; their declaration kinds, explicit binder order,
types, construction bodies and internal proof terms are unchanged. The
source's `noncomputable section` is retained. The unused `open KummerTheory`,
`open CyclicCohomology`, `universe u`, and group/typeclass section variables are
omitted: none occurs in the elaborated telescope or body of these five
commands. There are no implicit parameters, typeclass parameters or universe
parameters in these definitions. No local/private source command is needed.

The source imports of `Degree.FrobeniusLift` and `Degree.Norm` are replaced
by the published M008 definition module and the direct Mathlib import
`Mathlib.GroupTheory.QuotientGroup.Defs`. The resulting focused module uses
Mathlib's existing subgroup, range, image, quotient and additive homomorphism
constructions and canonical instances. It declares no new instance.
Exact-name searches found no existing NYLL declaration of these five names.
The new wrappers retain the specified source objects rather than introduce a
replacement interface. These import and namespace edits are the only
mathematical-context modifications.

This data unit does not contain the source membership theorem M025.005,
the full-value-group theorem M025.006, the quotient evaluation or bijectivity
theorems M025.009–010, `ValuationData`, or any subsequent normalized-valuation
results. It discharges no host class-formation, cup, transfer, Tate or
reciprocity target.

The Lean file retains the original copyright and author header. The retained
Apache-2.0 license is `licenses/NYLL/LICENSE`, SHA-256
`b40930bbcf80744c86c46a12bc9da056641d722716c378f5659b9e555ef833e1`,
and the notice is `licenses/NYLL/NOTICE`, SHA-256
`bf19eab77be48af60691e32428ed2126785de7d36f975d06f286d28d80f71e22`.
