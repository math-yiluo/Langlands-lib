# NYLL M009.012: finite-index additive subgroups

This module proves
`Langlands.NYLL.ClassFormation.zHatAddSubgroup_eq_mulNat_range_of_index_ne_zeroStatement`
with the source-adapted theorem
`Langlands.NYLL.ClassFormation.zHatAddSubgroup_eq_mulNat_range_of_index_ne_zero`.
Its explicit parameters are `(H : AddSubgroup ZHat)` followed by
`(hH : H.index ≠ 0)`. Its type is exactly the published statement applied to
these parameters, whose conclusion is
`H = (zHatMulNat H.index).toAddMonoidHom.range`.
The subgroup need not be given as closed.

The original is Naganori Yamaguchi's
`ClassFormation.zHatAddSubgroup_eq_mulNat_range_of_index_ne_zero`,
M009.012, lines 191–212 (signature 195–197) of
`Nyll/GaloisCohomology/ProfiniteIntegers/ProfiniteInteger.lean`, at commit
`fbd320cd8b1b06487c58227e92eb135794267709`. The file SHA-256 is
`b2fcb523b7bf0408b776c71df6d528d446d7d373634df6e5df43183d57fc5ae6`.
The registered source is `external-lean-reuse-snapshots-2026-10-21`,
fingerprint
`26e8c647ade044fe9bd4dd1f9d997d4ca12aaa4766e55ab31cb64ca9f8415e01`.

The canonical theorem reuses the already published theorem
`Langlands.NYLL.PortInternal.M009U014.zHatAddSubgroup_eq_mulNat_range_of_index_ne_zero`
with the same explicit parameters `H` and `hH`. Its equality is definitionally
the required statement application. The imported proof retains the source's
index argument: the multiplication range lies in `H`, has index `H.index`,
and therefore has relative index one in `H`.

The actual imports are
`Langlands.NYLL.GaloisCohomology.ProfiniteIntegers.ProfiniteInteger.Statements`
and
`Langlands.NYLL.GaloisCohomology.ProfiniteIntegers.ProfiniteInteger.U014.Proofs`.
Worker 242 isolated the canonical source-adapted entry and its exact published
statement type. During integration, the duplicate index argument was replaced
by the existing internal theorem. The canonical name, complete parameter list,
statement, topology and multiplication map are unchanged.

The original copyright and authorship header is retained. The Apache-2.0
license and source notice are in `licenses/NYLL/LICENSE` and
`licenses/NYLL/NOTICE`, with SHA-256 respectively
`b40930bbcf80744c86c46a12bc9da056641d722716c378f5659b9e555ef833e1`
and `bf19eab77be48af60691e32428ed2126785de7d36f975d06f286d28d80f71e22`.
