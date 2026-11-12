# NYLL M009: multiplication and finite-index subgroup targets

This module extracts eleven public theorem signatures of
`Nyll/GaloisCohomology/ProfiniteIntegers/ProfiniteInteger.lean`, pinned commit
`fbd320cd8b1b06487c58227e92eb135794267709`. Its file SHA-256 is
`b2fcb523b7bf0408b776c71df6d528d446d7d373634df6e5df43183d57fc5ae6`.
The registered source is `external-lean-reuse-snapshots-2026-10-21`, fingerprint
`26e8c647ade044fe9bd4dd1f9d997d4ca12aaa4766e55ab31cb64ca9f8415e01`.

All target names below have prefix `Langlands.NYLL.ClassFormation` and are
Prop-valued definitions. They use the actual published `ZHat : Type 0` closure
model, its canonical structures and coordinate maps, and the actual continuous
additive map `zHatMulNat`. No abstract completion, replacement topology or
freely supplied multiplication map is introduced.

| Unit | Source signature lines and name | Adapted target |
| --- | --- | --- |
| M009.001 | 31–33, `ClassFormation.proCIntegerOne_pow_nat_injective` | `proCIntegerOne_pow_nat_injectiveStatement` |
| M009.003 | 60–61, `ClassFormation.zHatMulNat_apply` | `zHatMulNat_applyStatement` |
| M009.005 | 89–90, `ClassFormation.zHatMulNat_injective` | `zHatMulNat_injectiveStatement` |
| M009.006 | 105–106, `ClassFormation.isClosed_zHatMulNat_range` | `isClosed_zHatMulNat_rangeStatement` |
| M009.008 | 119–120, `ClassFormation.zHatReduction_surjective` | `zHatReduction_surjectiveStatement` |
| M009.009 | 130–132, `ClassFormation.zHatMulNat_int` | `zHatMulNat_intStatement` |
| M009.010 | 139–141, `ClassFormation.zHatMulNat_range_eq_ker_reduction` | `zHatMulNat_range_eq_ker_reductionStatement` |
| M009.011 | 175–176, `ClassFormation.zHatMulNat_range_index` | `zHatMulNat_range_indexStatement` |
| M009.012 | 195–197, `ClassFormation.zHatAddSubgroup_eq_mulNat_range_of_index_ne_zero` | `zHatAddSubgroup_eq_mulNat_range_of_index_ne_zeroStatement` |
| M009.013 | 216–218, `ClassFormation.zHatAddSubgroup_eq_mulNat_range_of_index_eq` | `zHatAddSubgroup_eq_mulNat_range_of_index_eqStatement` |
| M009.014 | 225–227, `ClassFormation.zHatAddSubgroup_eq_mulNat_range_of_finite_quotient` | `zHatAddSubgroup_eq_mulNat_range_of_finite_quotientStatement` |

M009.001 has no parameters and asserts injectivity of natural powers of the
specified additive generator written multiplicatively. M009.003 has explicit
`n : ℕ` and `x : ZHat`. M009.005 has implicit `n` and explicit positivity
proof `hn`; M009.006 has explicit arbitrary `n`, including zero. Reduction
surjectivity and the range-kernel equality retain explicit `n` then `hn`.
The integer-multiplication rule has explicit `n` then `a : ℤ`.
The image-index target retains `n` then `hn` and uses the natural additive
subgroup index, not a cardinal-valued index.

The three subgroup-classification targets retain explicit `H`. M009.012 then
has explicit `hH : H.index ≠ 0`; M009.013 has implicit `n` followed by explicit
`hn : 0 < n` and `hindex : H.index = n`; M009.014 has the source instance
`[Finite (ZHat ⧸ H)]`. No closedness premise on `H` is inserted. The first and
third conclusions use `H.index`, and the second uses `n`. The equality
orientation is the source's `H = (zHatMulNat ...).toAddMonoidHom.range`.
All source premises, including those not used in a target definition's body,
remain in the target telescope.

Worker 120 prefixes the namespace with `Langlands.NYLL`, appends `Statement`
to source theorem names, omits proof bodies and theorem-only simp attributes,
and keeps the source noncomputable section. Four local unused-variable lint
settings retain the original premise names without changing their types.
The import set is reduced to the multiplication data module and Mathlib's
subgroup-index API. These imports state the targets without any M008 theorem
proof or earlier M009 theorem. Eventual proofs can have additional imports.

The module supplies no proofs. The private modular-arithmetic helper M009.004,
the separate integer-reduction computation M009.007, and the range equivalence,
division map and inverse laws M009.015–018 are outside this unit. No closure
discharge is claimed for those omitted units here. The related M008
integer-cast computation may support reuse of M009.007 once its exact proof
is published or a focused replacement is established in a dependent proof.
No host-model comparison or reciprocity theorem is asserted.

The original copyright, Apache-2.0 and author header is retained. See
`licenses/NYLL/LICENSE` (SHA-256
`b40930bbcf80744c86c46a12bc9da056641d722716c378f5659b9e555ef833e1`) and
`licenses/NYLL/NOTICE` (SHA-256
`bf19eab77be48af60691e32428ed2126785de7d36f975d06f286d28d80f71e22`).
