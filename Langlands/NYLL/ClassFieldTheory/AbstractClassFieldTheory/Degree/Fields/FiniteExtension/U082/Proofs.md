# NYLL M010.082: finite relative ramification cardinal

This proof adapts Naganori Yamaguchi, `n-yamaguchi-0729/ClassFieldTheory`,
pinned commit `fbd320cd8b1b06487c58227e92eb135794267709`,
`Nyll/ClassFieldTheory/AbstractClassFieldTheory/Degree/Fields.lean`,
lines 695–699 (M010.082, source-private `relativeRamificationIndexCardinal_lt_aleph0`),
with the private helpers at lines 654–687 (M010.079–080).
The file SHA-256 is
`841b30407b1f9f3eb64a30f6ccfa4f8ec555c791564a7e682b7c8ee23c2d156e`.
Registered source `external-lean-reuse-snapshots-2026-10-21` has content
fingerprint `26e8c647ade044fe9bd4dd1f9d997d4ca12aaa4766e55ab31cb64ca9f8415e01`;
the attribution supplement `nyll-classfieldtheory-fbd320cd-supplement`
has fingerprint
`a81005c3aceabc51e9193cdc643d4dd81dd9d496dca2a0cf0111ce610d5b0330`.

The theorem `Langlands.NYLL.PortInternal.M010.d082` has exactly
`Langlands.NYLL.PortInternal.M010.d082Statement E D` as its type.
Its parameters are implicit `{G : Type u} [Group G] [TopologicalSpace G]`,
then explicit `(E : FiniteAbstractExtension G)` and `(D : DegreeData G)`.
The finite-extension object carries finiteness of its actual relative
coset space. The conclusion bounds its relative ramification cardinal
strictly by `Cardinal.aleph0`, with no additional hypothesis.

The private `degreeCardinal_lt_aleph0` expands the degree to the cardinal
of the stored finite quotient and applies `Cardinal.lt_aleph0_of_finite`.
The private `relativeDegreeCardinals_lt_aleph0` proves that the residue
and ramification factors are nonzero: each is a cardinal of a nonempty
coset type, so `Cardinal.mk_ne_zero` applies; the residue lift stays
nonzero by `Cardinal.lift_eq_zero`. The cardinal fundamental identity
M010.035 identifies their product with the finite degree. Applying
`Cardinal.mul_lt_aleph0_iff_of_ne_zero` bounds both factors.
The ramification conclusion is the second conjunct, in the original universe of `G`.

The direct imports are the published
`Fields.FiniteExtension.CardinalFinitenessStatements` target and
`Fields.AbstractExtension.U035.Proofs` fundamental identity. Their
Mathlib dependencies supply the cardinal facts and quotient instances.
The two helpers remain private to this module, preserving the source
proof route without adding a duplicate public helper API.

Worker 183 retained the original copyright and author header, prefixed
the namespace, published the source-private target under its required
stable name, and used its published proposition as the theorem type.
The source `extensionSubgroup` abbreviation in the degree helper is
expanded to its exact `Subgroup.subgroupOf` body, as in the published
finite-extension data. See `licenses/NYLL/LICENSE`
(SHA-256 `b40930bbcf80744c86c46a12bc9da056641d722716c378f5659b9e555ef833e1`)
and `licenses/NYLL/NOTICE`
(SHA-256 `bf19eab77be48af60691e32428ed2126785de7d36f975d06f286d28d80f71e22`).
This support proof supplies no host reciprocity assertion.
